use core::{
  ops::{Add, AddAssign, Neg, Sub, SubAssign, Mul, MulAssign},
  iter::Sum,
};

use rand_core::RngCore;

use zeroize::Zeroize;
use subtle::{Choice, CtOption, ConstantTimeEq, ConditionallySelectable, ConditionallyNegatable};
use crypto_bigint::{U256, modular::constant_mod::Residue};

use crate::U256H;

use group::{
  ff::{Field, PrimeField, PrimeFieldBits},
  Group, GroupEncoding,
  prime::PrimeGroup,
};

use crate::{
  field::HelioseleneField,
  Field25519,
  field::FieldExtensions
};

/*
=================================
              NOTE
=================================
The lazy reduction's bleeding edge was searched for, and seems to have been found in my testing.
That being said, if there are indeed 0.00n% edge cases where this math fails with point combinations,
this can be mitigated by forcing addition to reduce_weak() at the end of each add/sub in field.rs at 
the return points of add() and sub().

My bounds analysis and anectodal spamming of the crate testing via cargo seems to indicate that should
not be necessary, but as always, I could be wrong as I don't know everything.
*/

macro_rules! curve {
  (
    $Scalar: ident,
    $Field: ident,
    $Point: ident,
  ) => {
    /// Point.
    #[derive(Clone, Copy, Debug, Zeroize)]
    #[repr(C)]
    pub struct $Point {
      pub x: $Field, // / Z
      pub y: $Field, // / Z
      pub z: $Field,
    }

    impl ConstantTimeEq for $Point {
      fn ct_eq(&self, other: &Self) -> Choice {
        let x1 = self.x * other.z;
        let x2 = other.x * self.z;

        let y1 = self.y * other.z;
        let y2 = other.y * self.z;

        (self.x.is_zero() & other.x.is_zero()) | (x1.ct_eq(&x2) & y1.ct_eq(&y2))
      }
    }

    impl PartialEq for $Point {
      fn eq(&self, other: &$Point) -> bool {
        self.ct_eq(other).into()
      }
    }

    impl Eq for $Point {}

    impl ConditionallySelectable for $Point {
      fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        $Point {
          x: $Field::conditional_select(&a.x, &b.x, choice),
          y: $Field::conditional_select(&a.y, &b.y, choice),
          z: $Field::conditional_select(&a.z, &b.z, choice),
        }
      }
    }

    impl $Point {
      pub fn coords(&self) -> ($Field, $Field, $Field) {
        (self.x, self.y, self.z)
      }
    }

    impl Add for $Point {
      type Output = $Point;

      /*
      Batching the operation/reduction sections seems to please the compiler. Along with the innate benefit
      that comes from lazy reduction for helioselene, here are some other notes on what makes this faster:
      - All functional constants labelled as such globally, eliminating recomputation ovberhead for both curves
      - Field * A is the same as Field.triple().negate(), allowing us to eliminate muls for these a=-3 curves
      */
      #[allow(non_snake_case)]
      fn add(self, other: Self) -> Self {
        let X1 = self.x;
        let Y1 = self.y;
        let Z1 = self.z;
        let X2 = other.x;
        let Y2 = other.y;
        let Z2 = other.z;

        let t0 = X1 * X2;
        let t1 = Y1 * Y2;
        let t2 = Z1 * Z2;
        
        let sum_xy1 = X1 + Y1;
        let sum_xy2 = X2 + Y2;
        let sum_xz1 = X1 + Z1;
        let sum_xz2 = X2 + Z2;
        let sum_yz1 = Y1 + Z1;
        let sum_yz2 = Y2 + Z2;
        
        let sum_xy1 = sum_xy1.reduce_weak();
        let sum_xy2 = sum_xy2.reduce_weak();
        let sum_xz1 = sum_xz1.reduce_weak();
        let sum_xz2 = sum_xz2.reduce_weak();
        let sum_yz1 = sum_yz1.reduce_weak();
        let sum_yz2 = sum_yz2.reduce_weak();
        
        let prod_xy = sum_xy1 * sum_xy2;
        let prod_xz = sum_xz1 * sum_xz2;
        let prod_yz = sum_yz1 * sum_yz2;
        
        let t3 = prod_xy - t0 - t1;
        let t4 = prod_xz - t0 - t2;
        let t5 = prod_yz - t1 - t2;
        
        let t3 = t3.reduce_weak();
        let t4 = t4.reduce_weak();
        let t5 = t5.reduce_weak();
        
        let Z3_tmp = (t4+t4+t4).neg();
        let X3_tmp = B3 * t2;
        let Z3_new = (X3_tmp + Z3_tmp).reduce_weak();
        let X3_new = (t1 - Z3_new).reduce_weak();
        let Z3_final = (t1 + Z3_new).reduce_weak();
        let Y3 = X3_new * Z3_final;
        
        let t2_a = (t2+t2+t2).neg();
        let t4_b3 = (B3 * t4);
        let t1_new = (t0 + t0 + t0 + t2_a).reduce_weak();

        let t2_temp = (t0 - t2_a).reduce_weak();
        let t2_new = (t2_temp + t2_temp+t2_temp).neg();
        let t4_new = (t4_b3 + t2_new).reduce_weak();
        let t0_new = t1_new * t4_new;
        let Y3_final = Y3 + t0_new;
        
        let t0_final = t5 * t4_new;
        let X3_final = (t3 * X3_new - t0_final);
        let t0_last = t3 * t1_new;
        let Z3_result = t5 * Z3_final + t0_last;
        
        $Point { x: X3_final.reduce_weak(), y: Y3_final.reduce_weak(), z: Z3_result.reduce_weak()}
      }
    }

    impl AddAssign for $Point {
      fn add_assign(&mut self, other: $Point) {
        *self = *self + other;
      }
    }

    impl Add<&$Point> for $Point {
      type Output = $Point;
      fn add(self, other: &$Point) -> $Point {
        self + *other
      }
    }

    impl AddAssign<&$Point> for $Point {
      fn add_assign(&mut self, other: &$Point) {
        *self += *other;
      }
    }

    impl Neg for $Point {
      type Output = $Point;
      fn neg(self) -> Self {
        $Point { x: self.x, y: -self.y, z: self.z }
      }
    }

    impl Sub for $Point {
      type Output = $Point;
      #[allow(clippy::suspicious_arithmetic_impl)]
      fn sub(self, other: Self) -> Self {
        (self + other.neg())
      }
    }

    impl SubAssign for $Point {
      fn sub_assign(&mut self, other: $Point) {
        *self = *self - other;
      }
    }

    impl Sub<&$Point> for $Point {
      type Output = $Point;
      fn sub(self, other: &$Point) -> $Point {
        self - *other
      }
    }

    impl SubAssign<&$Point> for $Point {
      fn sub_assign(&mut self, other: &$Point) {
        *self -= *other;
      }
    }

    impl Group for $Point {
      type Scalar = $Scalar;
      fn random(mut rng: impl RngCore) -> Self {
        loop {
          let mut bytes = $Field::random(&mut rng).to_repr();
          let mut_ref: &mut [u8] = bytes.as_mut();
          mut_ref[31] |= u8::try_from(rng.next_u32() % 2).unwrap() << 7;
          let opt = Self::from_bytes(&bytes);
          if opt.is_some().into() {
            return opt.unwrap();
          }
        }
      }
      fn identity() -> Self {
        $Point { x: $Field::ZERO, y: $Field::ONE, z: $Field::ZERO }
      }
      fn generator() -> Self {
        G
      }
      fn is_identity(&self) -> Choice {
        self.x.is_zero()
      }

      #[allow(non_snake_case)]
      #[inline(always)]

      // Same algorithm, just restructured for lazy reduction friendliness.
      fn double(&self) -> Self {
        // dbl-2007-bl-2
        let X1 = self.x;
        let Y1 = self.y;
        let Z1 = self.z;

        let XX = X1.square();
        let ZZ = Z1.square();
        
        let w = (XX - ZZ).reduce_weak();
        let w3 = w + w + w;
        
        let zy = Y1 * Z1;
        let s = zy + zy;
        
        let s_squared = s.square();
        let w3_squared = w3.square();
        
        let sss = s * s_squared;
        
        let R = Y1 * s;
        
        let RR = R.square();
        
        let xr = X1 * R;
        let B_ = xr + xr;
        let h = (w3_squared - (B_ + B_)).reduce_weak();
        
        let X3 = h * s;
        let Y3 = w3 * (B_ - h).reduce_weak() - (RR + RR);
        let Z3 = sss;

        let res = Self { 
          x: X3, 
          y: Y3.reduce_weak(), 
          z: Z3 
        };
        
        Self::conditional_select(&res, &Self::identity(), self.is_identity())
      }
    }

    impl $Point {
      const ID: Self = Self { x: $Field::ZERO, y: $Field::ONE, z: $Field::ZERO };
    }

    impl Sum<$Point> for $Point {
      fn sum<I: Iterator<Item = $Point>>(iter: I) -> $Point {
        let mut res = Self::identity();
        for i in iter {
          res += i;
        }
        res
      }
    }

    impl<'a> Sum<&'a $Point> for $Point {
      fn sum<I: Iterator<Item = &'a $Point>>(iter: I) -> $Point {
        $Point::sum(iter.cloned())
      }
    }

    impl Mul<$Scalar> for $Point {
      type Output = $Point;
      
      // Restructured for cache friendliness and efficient table precomputation with double()
      fn mul(self, mut scalar: $Scalar) -> $Point {
        let mut table = [$Point::ID; 16];
        table[0] = $Point::ID;
        table[1] = self;
        table[2] = self.double();
        table[3] = table[2] + self;
        table[4] = table[2].double();
        table[5] = table[4] + self;
        table[6] = table[4] + table[2];
        table[7] = table[6] + self;
        table[8] = table[4].double(); 
        table[9] = table[8] + self; 
        table[10] = table[8] + table[2];
        table[11] = table[10] + self;
        table[12] = table[8] + table[4];
        table[13] = table[12] + self;
        table[14] = table[12] + table[2];
        table[15] = table[14] + self;

        let mut res = Self::ID;
        let scalar_bits = scalar.to_le_bits();
          
        for window in (0..64).rev() {
          if window != 63 {
            res = res.double().double().double().double()
          }
          
          let bit_offset = window * 4;
          let mut bits = 0u8;
          bits |= scalar_bits[bit_offset] as u8;
          bits |= (scalar_bits[bit_offset + 1] as u8) << 1;
          bits |= (scalar_bits[bit_offset + 2] as u8) << 2;
          bits |= (scalar_bits[bit_offset + 3] as u8) << 3;
          
          let mut term = table[0];
          for (j, candidate) in table[1 ..].iter().enumerate() {
            let j = j + 1;
            term = Self::conditional_select(&term, &candidate, usize::from(bits).ct_eq(&j));
          }
          res += term;
        }

        scalar.zeroize();
        res
      }
    }

    impl MulAssign<$Scalar> for $Point {
      fn mul_assign(&mut self, other: $Scalar) {
        *self = *self * other;
      }
    }

    impl Mul<&$Scalar> for $Point {
      type Output = $Point;
      fn mul(self, other: &$Scalar) -> $Point {
        self * *other
      }
    }

    impl MulAssign<&$Scalar> for $Point {
      fn mul_assign(&mut self, other: &$Scalar) {
        *self *= *other;
      }
    }

    impl GroupEncoding for $Point {
      type Repr = <$Field as PrimeField>::Repr;

      fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        // Extract and clear the sign bit
        let sign = Choice::from(bytes[31] >> 7);
        let mut bytes = *bytes;
        let mut_ref: &mut [u8] = bytes.as_mut();
        mut_ref[31] &= !(1 << 7);

        // Parse x, recover y
        $Field::from_repr(bytes).and_then(|x| {
          let is_identity = x.is_zero();

          let y = recover_y(x).map(|mut y| {
            y.conditional_negate(y.is_odd().ct_eq(&!sign));
            y
          });

          // If this the identity, set y to 1
          let y =
            CtOption::conditional_select(&y, &CtOption::new($Field::ONE, 1.into()), is_identity);
          // Create the point if we have a y solution
          let point = y.map(|y| $Point { x, y, z: $Field::ONE });

          let not_negative_zero = !(is_identity & sign);
          // Only return the point if it isn't -0
          CtOption::conditional_select(
            &CtOption::new($Point::identity(), 0.into()),
            &point,
            not_negative_zero,
          )
        })
      }

      fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        $Point::from_bytes(bytes)
      }

      fn to_bytes(&self) -> Self::Repr {
        let Some(z) = Option::<$Field>::from(self.z.invert()) else { return [0; 32] };
        let x = self.x * z;
        let y = self.y * z;

        let mut bytes = x.to_repr();
        let mut_ref: &mut [u8] = bytes.as_mut();

        // Normalize the sign to 0 when x is 0
        let y_sign = u8::conditional_select(&y.is_odd().unwrap_u8(), &0, x.ct_eq(&$Field::ZERO));
        mut_ref[31] |= y_sign << 7;
        bytes
      }
    }

    impl PrimeGroup for $Point {}

    impl ec_divisors::DivisorCurve for $Point {
      type FieldElement = $Field;

      fn a() -> Self::FieldElement {
        -$Field::from(3u64)
      }
      fn b() -> Self::FieldElement {
        B
      }

      fn to_xy(point: Self) -> Option<(Self::FieldElement, Self::FieldElement)> {
        let z: Self::FieldElement = Option::from(point.z.invert())?;
        Some((point.x * z, point.y * z))
      }
    }
  };
}

// Generator points and B constants declared globally inline to avoid wasteful recomputation. Hex was pre-calculated
// and fed here manually.
mod helios {
  use super::*;

  curve!(
    HelioseleneField,
    Field25519,
    HeliosPoint,
  );

  const G_X: Field25519 = Field25519(Residue::new(&U256::from_be_hex("0000000000000000000000000000000000000000000000000000000000000003")));
  const G_Y: Field25519 = Field25519(Residue::new(&U256::from_be_hex("537b74d97ac0721cbd92668350205f0759003bddc586a5dcd243e639e3183ef4")));
  // const A: Field25519 = Field25519(Residue::new(&U256::from_be_hex("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffea")));
  const B: Field25519 = Field25519(Residue::new(&U256::from_be_hex("22e8c739b0ea70b8be94a76b3ebb7b3b043f6f384113bf3522b49ee1edd73ad4")));
  const B3: Field25519 = Field25519(Residue::new(&U256::from_be_hex("68ba55ad12bf522a3bbdf641bc3271b10cbe4da8c33b3d9f681ddca5c985b07c")));
  const G: HeliosPoint = HeliosPoint { x: G_X, y: G_Y, z: Field25519::ONE };

  fn recover_y(x: Field25519) -> CtOption<Field25519> {
    ((x.pow2k(1) * x) - x - x - x + B).sqrt_fast()
  }

  #[test]
  fn test_helios() {
    ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut rand_core::OsRng);
  }

  #[test]
  fn generator_helios() {
    use helios::{G_X, G_Y, G};
    assert!(G.x == G_X);
    assert!(G.y == G_Y);
    assert!(recover_y(G.x).unwrap() == -G.y);
  }

  #[test]
  fn zero_x_is_invalid() {
    assert!(Option::<Field25519>::from(recover_y(Field25519::ZERO)).is_none());
  }
}
pub use helios::HeliosPoint;

mod selene {
  use super::*;

  curve!(
    Field25519,
    HelioseleneField,
    SelenePoint,
  );

  const G_X: HelioseleneField = HelioseleneField::from_u256(U256H::from_be_hex("0000000000000000000000000000000000000000000000000000000000000001"));
  const G_Y: HelioseleneField = HelioseleneField::from_u256(U256H::from_be_hex("7a19d927b85cca9257c93177455c825f938bb198c8f09b37741e0aa6a1d3fdd2"));
  // const A: HelioseleneField = HelioseleneField::from_u256(U256H::from_be_hex("7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79c"));
  const B: HelioseleneField = HelioseleneField::from_u256(U256H::from_be_hex("70127713695876c17f51bba595ffe279f3944bdf06ae900e68de0983cb5a4558"));
  const B3: HelioseleneField = HelioseleneField::from_u256(U256H::from_be_hex("5037653a3c0964447df532f0c1ffa76e5bbdf343a540d97a5d2c77a66fbf40ca"));
  const G: SelenePoint = SelenePoint { x: G_X, y: G_Y, z: HelioseleneField::ONE };

  fn recover_y(x: HelioseleneField) -> CtOption<HelioseleneField> {
    ((x.square() * x) - x - x - x + B).sqrt()
  }

  #[test]
  fn test_selene() {
    ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut rand_core::OsRng);
  }

  #[test]
  fn generator_selene() {
    use selene::{G_X, G_Y, G};
    assert!(G.x == G_X);
    assert!(G.y == G_Y);
    assert!(recover_y(G.x).unwrap() == G.y);
  }

  #[test]
  fn zero_x_is_invalid() {
    assert!(Option::<HelioseleneField>::from(recover_y(HelioseleneField::ZERO)).is_none());
  }
}
pub use selene::SelenePoint;

// Checks random won't infinitely loop
#[test]
fn random() {
  HeliosPoint::random(&mut rand_core::OsRng);
  SelenePoint::random(&mut rand_core::OsRng);
}

