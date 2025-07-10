use zeroize::Zeroize;

// Use black_box when possible
#[rustversion::since(1.66)]
use core::hint::black_box;
#[rustversion::before(1.66)]
fn black_box<T>(val: T) -> T {
  val
}

pub(crate) fn u8_from_bool(bit_ref: &mut bool) -> u8 {
  let bit_ref = black_box(bit_ref);

  let mut bit = black_box(*bit_ref);
  let res = black_box(bit as u8);
  bit.zeroize();
  debug_assert!((res | 1) == 1);

  bit_ref.zeroize();
  res
}

macro_rules! math_op {
  (
    $Value: ident,
    $Other: ident,
    $Op: ident,
    $op_fn: ident,
    $Assign: ident,
    $assign_fn: ident,
    $function: expr
  ) => {
    impl $Op<$Other> for $Value {
      type Output = $Value;
      fn $op_fn(self, other: $Other) -> Self::Output {
        Self($function(self.0, other.0))
      }
    }
    impl $Assign<$Other> for $Value {
      fn $assign_fn(&mut self, other: $Other) {
        self.0 = $function(self.0, other.0);
      }
    }
    impl<'a> $Op<&'a $Other> for $Value {
      type Output = $Value;
      fn $op_fn(self, other: &'a $Other) -> Self::Output {
        Self($function(self.0, other.0))
      }
    }
    impl<'a> $Assign<&'a $Other> for $Value {
      fn $assign_fn(&mut self, other: &'a $Other) {
        self.0 = $function(self.0, other.0);
      }
    }
  };
}

macro_rules! from_wrapper {
  ($wrapper: ident, $uint: ident) => {
    impl From<$uint> for $wrapper {
      fn from(a: $uint) -> $wrapper {
        Self::from_u256(U256::from(a).into())
      }
    }
  };
}

macro_rules! field {
  (
    $FieldName: ident,
    $ResidueType: ident,

    $MODULUS_STR: ident,
    $MODULUS: ident,
    $WIDE_MODULUS: ident,

    $MULTIPLICATIVE_GENERATOR: literal,
    $S: literal,
    $TWO_INV: literal,
    $ROOT_OF_UNITY: literal,
    $ROOT_OF_UNITY_INV: literal,
    $DELTA: literal,
  ) => {
    impl ConstantTimeEq for $FieldName {
      fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
      }
    }

    impl ConditionallySelectable for $FieldName {
      fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        $FieldName(Limbs51::conditional_select(&a.0, &b.0, choice))
      }
    }

    impl DefaultIsZeroes for $FieldName {}

    math_op!($FieldName, $FieldName, Add, add, AddAssign, add_assign, |x: Limbs51, y| x
      .add(y));
    math_op!($FieldName, $FieldName, Sub, sub, SubAssign, sub_assign, |x: Limbs51, y| x
      .sub(y));
    math_op!($FieldName, $FieldName, Mul, mul, MulAssign, mul_assign, |x: Limbs51, y| x
      .mul(y));

    from_wrapper!($FieldName, u8);
    from_wrapper!($FieldName, u16);
    from_wrapper!($FieldName, u32);
    from_wrapper!($FieldName, u64);
    from_wrapper!($FieldName, u128);

    impl Neg for $FieldName {
      type Output = $FieldName;
      fn neg(self) -> $FieldName {
        Self(self.0.neg())
      }
    }

    impl<'a> Neg for &'a $FieldName {
      type Output = $FieldName;
      fn neg(self) -> Self::Output {
        (*self).neg()
      }
    }

    impl $FieldName {
      pub fn from_res(residue: $ResidueType) -> Self {
        let bytes = residue.retrieve().to_le_bytes();
        Self::from_bytes(&bytes)
      }
      
      // allow for compile-time declarations through u256h
      pub const fn from_u256(val: U256H) -> Self {
        const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;

        let limbs = [
          val.limbs[0] & LOW_51_BIT_MASK,
          ((val.limbs[0] >> 51) | (val.limbs[1] << 13)) & LOW_51_BIT_MASK,
          ((val.limbs[1] >> 38) | (val.limbs[2] << 26)) & LOW_51_BIT_MASK,
          ((val.limbs[2] >> 25) | (val.limbs[3] << 39)) & LOW_51_BIT_MASK,
          (val.limbs[3] >> 12) & LOW_51_BIT_MASK,
        ];

        Self(Limbs51::new(limbs))
      }

      pub fn reduce_weak(self) -> Self {
        Self(self.0.reduce_weak())
      }

      pub fn propogate_carries(self) -> Self {
        Self(self.0.propogate_carries())
      }

      pub fn from_bytes(bytes: &[u8; 32]) -> Self {
        let load8 = |input: &[u8]| -> u64 {
          u64::from_le_bytes(input.try_into().unwrap())
        };

        const LOW_51_BIT_MASK: u64 = (1u64 << 51) - 1;
        
        $FieldName(
          Limbs51::new([
            load8(&bytes[0..8]) & LOW_51_BIT_MASK,
            (load8(&bytes[6..14]) >> 3) & LOW_51_BIT_MASK,
            (load8(&bytes[12..20]) >> 6) & LOW_51_BIT_MASK,
            (load8(&bytes[19..27]) >> 1) & LOW_51_BIT_MASK,
            (load8(&bytes[24..32]) >> 12) & LOW_51_BIT_MASK,
          ])
        )
      }

      pub fn to_bytes(&self) -> [u8; 32] {
        self.0.to_bytes()
      }

      // Restructured for cache friendliness and unrolling, reducing WASM cycles
      pub fn pow(&self, other: $FieldName) -> $FieldName {
        let mut table = [Self(Limbs51::ONE); 16];
        table[1] = *self;
        table[2] = table[1] * self;
        table[3] = table[2] * self;
        table[4] = table[3] * self;
        table[5] = table[4] * self;
        table[6] = table[5] * self;
        table[7] = table[6] * self;
        table[8] = table[7] * self;
        table[9] = table[8] * self;
        table[10] = table[9] * self;
        table[11] = table[10] * self;
        table[12] = table[11] * self;
        table[13] = table[12] * self;
        table[14] = table[13] * self;
        table[15] = table[14] * self;

        let mut res = Self(Limbs51::ONE);
        let exp_bytes = other.to_bytes();
        
        for window in (0..64).rev() {
          if window != 63 {
            res = res.square().square().square().square();
          }
          
          let bit_offset = window * 4;
          let mut bits = 0u8;
          bits |= (exp_bytes[bit_offset / 8] >> (bit_offset % 8)) & 1;
          bits |= ((exp_bytes[(bit_offset + 1) / 8] >> ((bit_offset + 1) % 8)) & 1) << 1;
          bits |= ((exp_bytes[(bit_offset + 2) / 8] >> ((bit_offset + 2) % 8)) & 1) << 2;
          bits |= ((exp_bytes[(bit_offset + 3) / 8] >> ((bit_offset + 3) % 8)) & 1) << 3;
          
          let bits_usize = bits as usize;
          
          let mut factor = table[0];
          for i in 1..16 {
            let choice = (bits_usize).ct_eq(&i);
            factor = Self::conditional_select(&factor, &table[i], choice);
          }
          
          res *= factor;
          bits.zeroize();
        }
        
        res
      }

      pub fn pow2k(&self, k: usize) -> Self {
        Self(self.0.pow2k(k as u32))
      }
    }

    impl Sum<$FieldName> for $FieldName {
      fn sum<I: Iterator<Item = $FieldName>>(iter: I) -> $FieldName {
        let mut res = $FieldName::ZERO;
        for item in iter {
          res += item;
        }
        res
      }
    }

    impl<'a> Sum<&'a $FieldName> for $FieldName {
      fn sum<I: Iterator<Item = &'a $FieldName>>(iter: I) -> $FieldName {
        iter.cloned().sum()
      }
    }

    impl Product<$FieldName> for $FieldName {
      fn product<I: Iterator<Item = $FieldName>>(iter: I) -> $FieldName {
        let mut res = $FieldName::ONE;
        for item in iter {
          res *= item;
        }
        res
      }
    }

    impl<'a> Product<&'a $FieldName> for $FieldName {
      fn product<I: Iterator<Item = &'a $FieldName>>(iter: I) -> $FieldName {
        iter.cloned().product()
      }
    }

    impl PrimeField for $FieldName {
      type Repr = [u8; 32];

      const MODULUS: &'static str = $MODULUS_STR;

      const NUM_BITS: u32 = 255;
      const CAPACITY: u32 = 254;

      const TWO_INV: Self = $FieldName::from_u256(U256H::from_be_hex($TWO_INV));

      const MULTIPLICATIVE_GENERATOR: Self =
        Self::from_u256(U256H{limbs: [$MULTIPLICATIVE_GENERATOR, 0, 0, 0]});
      const S: u32 = $S;

      const ROOT_OF_UNITY: Self = $FieldName::from_u256(U256H::from_be_hex($ROOT_OF_UNITY));
      const ROOT_OF_UNITY_INV: Self = $FieldName::from_u256(U256H::from_be_hex($ROOT_OF_UNITY_INV));

      const DELTA: Self = $FieldName::from_u256(U256H::from_be_hex($DELTA));

      fn from_repr(bytes: Self::Repr) -> CtOption<Self> {
        let res = U256::from_le_slice(&bytes);
        CtOption::new($FieldName::from_u256(res.into()), res.ct_lt(&$MODULUS))
      }
      fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
      }

      fn is_odd(&self) -> Choice {
        self.0.is_odd()
      }
    }

    impl PrimeFieldBits for $FieldName {
      type ReprBits = [u8; 32];

      fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        self.to_repr().into()
      }

      fn char_le_bits() -> FieldBits<Self::ReprBits> {
        let mut repr = [0; 32];
        repr.copy_from_slice(&$MODULUS.to_le_bytes());
        repr.into()
      }
    }
  };
}