use zeroize::{DefaultIsZeroes, Zeroize};
use crate::backend::u8_from_bool;

use crypto_bigint::{
  U256, U512,
  modular::constant_mod::{ResidueParams, Residue},
};

use core::{
  ops::{Add, AddAssign, Neg, Sub, SubAssign, Mul, MulAssign, Shr},
  iter::{Sum, Product},
};

use subtle::{Choice, CtOption, ConstantTimeEq, ConstantTimeLess, ConditionallySelectable};
use rand_core::RngCore;
use crate::U256H;

use crypto_bigint::{Encoding, NonZero, Limb, impl_modulus};

use ff::{Field, PrimeField, FieldBits, PrimeFieldBits, helpers::sqrt_ratio_generic};

const MODULUS_STR: &str = "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

// C where 2^255 - C = Helioselene Prime.
const C_1X: u128 = 0x408087d3489a94a791492d8d86d83861u128;
// C for Barrett, which is measured against 2^256. Works out to be exactly 2x the above.
const C_2X: u128 = 0x81010fa69135294f22925b1b0db070c2u128;

// ====================================================================
// 51-bit limb handling, for lazy reduction
// ====================================================================
#[derive(Default, Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
#[repr(C)]
pub struct Limbs51(pub(crate) [u64; 5]);

impl Limbs51 {
  pub const ZERO: Self = Self([0, 0, 0, 0, 0]);
  pub const ONE: Self = Self([1, 0, 0, 0, 0]);
  const MASK_51: u64 = (1u64 << 51) - 1;

  /*
  Mathematically derived constants that weak reduce to Helioselene Prime, allowing for efficient underflow protection 
  when subtracting with lazy reduction. I went aggressive to opt for fully lazy reduction in sub as opposed to reducing
  at the end of every - operator, as the point math is contained enough to justify manual management of
  intermediate terms.

  These can also be used to negate the sign of any Limbs51 object mod Prime.
  */

  const P_MUL: [u64; 5] = {
    [
      35227423003671024, 
      34180289646353758, 
      36028796748422652, 
      36028797018963952, 
      36028797018963952
    ]
  };

  pub const fn new(limbs: [u64; 5]) -> Self {
    Self(limbs)
  }

  #[inline(always)]
  pub fn square(&self) -> Self {
    *self * *self
  }

  /*
  Multiply + reduce in the same operation, leveraging the full u256-wide version of the reduction constant.
  Operates in native 5-limb space where possible, allowing for Barrett reduction and propogation without
  conversion overhead for each call.

  Simpler multiplication with 5-limb representation is possible, and it is fast, but with C as a 128-bit number,
  performance falls apart. This created the demand for a Barrett system that works on 5 limbs natively as an alternative,
  clawing back precious performance, and making room for more aggressive chaining due to the reduction traits.
  */

  #[inline(always)]
  pub fn mul_barrett(&self, rhs: &Self) -> Self {
    let a_reduced = self.reduce_weak();
    let b_reduced = rhs.reduce_weak();
    
    let a_4x64 = a_reduced.to_4x64();
    let b_4x64 = b_reduced.to_4x64();
    
    // Step 1: Full multiplication
    let (low, high) = Self::mul_wide_u256(&a_4x64, &b_4x64);
    
    // Step 2: Barrett reduction
    let (reduction, overflow) = high.mul_by_u128_with_overflow_u128(C_2X);
    
    // Step 3: Calculate overflow_reduced
    let overflow_reduced = U256H::from_u128(overflow).mul_by_u128(C_2X);
    
    // Step 4: Build combined value (low + reduction + overflow_reduced)
    let mut combined = [0u64; 5];
    
    // Single pass addition
    let mut carry = 0u128;
    
    for i in 0..4 {
        let sum = (low.limbs[i] as u128) + 
                  (reduction.limbs[i] as u128) + 
                  (overflow_reduced.limbs[i] as u128) + 
                  carry;
        combined[i] = sum as u64;
        carry = sum >> 64;
    }
    combined[4] = carry as u64;
    
    // Propogate carries across limbs, both from the Barrett POV and the final limb POV
    let c_lo = C_2X as u64;
    let c_hi = (C_2X >> 64) as u64;
    
    let prod_lo = (combined[4] as u128) * (c_lo as u128);
    let prod_hi = (combined[4] as u128) * (c_hi as u128);
    
    let lo64 = prod_lo as u64;
    let mid64 = (prod_lo >> 64) as u64 + (prod_hi as u64);
    let hi_bit = (prod_hi >> 64) as u64;
    
    carry = 0;
    
    let sum = (combined[0] as u128) + (lo64 as u128) + carry;
    combined[0] = sum as u64;
    carry = sum >> 64;
    
    let sum = (combined[1] as u128) + (mid64 as u128) + carry;
    combined[1] = sum as u64;
    carry = sum >> 64;
    
    let sum = (combined[2] as u128) + (hi_bit as u128) + carry;
    combined[2] = sum as u64;
    carry = sum >> 64;
    
    combined[3] += carry as u64;
    combined[4] = 0;
    
    let mut limbs_5x51 = [0u64; 5];
    
    limbs_5x51[0] = combined[0] & Self::MASK_51;
    limbs_5x51[1] = ((combined[0] >> 51) | (combined[1] << 13)) & Self::MASK_51;
    limbs_5x51[2] = ((combined[1] >> 38) | (combined[2] << 26)) & Self::MASK_51;
    limbs_5x51[3] = ((combined[2] >> 25) | (combined[3] << 39)) & Self::MASK_51;
    limbs_5x51[4] = (combined[3] >> 12) & Self::MASK_51;

    let final_carry = combined[3] >> 63;

    let mask1 = 0u64.wrapping_sub(final_carry.min(1));
    let mask2 = 0u64.wrapping_sub(final_carry / 2);

    let c_full_lo = C_1X as u64;
    let c_full_hi = (C_1X >> 64) as u64;

    let carry_lo = (c_full_lo & mask1) + (c_full_lo & mask2);
    let carry_hi = (c_full_hi & mask1) + (c_full_hi & mask2);

    let carry_lo51 = carry_lo & Self::MASK_51;
    let carry_mi51 = ((carry_lo >> 51) | (carry_hi << 13)) & Self::MASK_51;
    let carry_hi51 = (carry_hi >> 38) & Self::MASK_51;

    let mut c = 0u64;

    let sum = (limbs_5x51[0] as u128) + (carry_lo51 as u128);
    limbs_5x51[0] = (sum & Self::MASK_51 as u128) as u64;
    c = (sum >> 51) as u64;

    let sum = (limbs_5x51[1] as u128) + (carry_mi51 as u128) + (c as u128);
    limbs_5x51[1] = (sum & Self::MASK_51 as u128) as u64;
    c = (sum >> 51) as u64;

    let sum = (limbs_5x51[2] as u128) + (carry_hi51 as u128) + (c as u128);
    limbs_5x51[2] = (sum & Self::MASK_51 as u128) as u64;
    c = (sum >> 51) as u64;

    limbs_5x51[3] += c;
    
    Self(limbs_5x51)
  }
    
  // Helper to re-condense into u64x4 representation without needing to_bytes, preserving lazy reduction capability.
  #[inline(always)]
  fn to_4x64(&self) -> [u64; 4] {
    let mut result = [0u64; 4];
    

    result[0] = self.0[0] | (self.0[1] << 51);
    result[1] = (self.0[1] >> 13) | (self.0[2] << 38);
    result[2] = (self.0[2] >> 26) | (self.0[3] << 25);
    result[3] = (self.0[3] >> 39) | (self.0[4] << 12);
    
    result
  }
    
  // Multiply 2 4x64 representations without creating a U256H first.
  #[inline(always)]
  fn mul_wide_u256(a: &[u64; 4], b: &[u64; 4]) -> (U256H, U256H) {
    let mut result = [0u64; 8];
    
    for i in 0..4 {
      let mut carry = 0u128;
      for j in 0..4 {
        let product = (a[i] as u128) * (b[j] as u128);
        let sum = (result[i + j] as u128) + product + carry;
        result[i + j] = sum as u64;
        carry = sum >> 64;
      }
      result[i + 4] = carry as u64;
    }
    
    let low = U256H { limbs: [result[0], result[1], result[2], result[3]] };
    let high = U256H { limbs: [result[4], result[5], result[6], result[7]] };
    
    (low, high)
  }
    
  // Return to 5x51 bit limbs from a valid 4x64 dataset.
  #[inline(always)]
  fn from_4x64_to_5x51(limbs_4x64: &[u64; 4]) -> Self {
    let mut result = [0u64; 5];
    
    result[0] = limbs_4x64[0] & Self::MASK_51;
    result[1] = ((limbs_4x64[0] >> 51) | (limbs_4x64[1] << 13)) & Self::MASK_51;
    result[2] = ((limbs_4x64[1] >> 38) | (limbs_4x64[2] << 26)) & Self::MASK_51;
    result[3] = ((limbs_4x64[2] >> 25) | (limbs_4x64[3] << 39)) & Self::MASK_51;
    result[4] = (limbs_4x64[3] >> 12) & Self::MASK_51;
    
    Self(result)
  }

  // Helper for chaining .square()
  #[inline(always)]
  pub fn pow2k(&self, mut k: u32) -> Self {
    debug_assert!(k > 0);
    
    let mut a = *self;
    
    loop {
      a = a.square();
      
      k -= 1;
      if k == 0 {
        break;
      }
    }
    
    a
  }

  // Check if Limbs51 mod Prime == 0
  pub(crate) fn is_zero(&self) -> Choice {
    let reduced = self.reduce_canonical();
    Choice::from(u8_from_bool(&mut (reduced == Self::ZERO)))
  }

  /*
  Can be used when lower limbs get filled to the point of overflow, to propogate across the limbs of the intermediates when lazy reduction
  is needed for very large addition chains with limited limb spread, to prevent limb overflow bugs without the overhead of full weak reduce.
  */

  #[inline(always)]
  pub fn propogate_carries(&self) -> Self {
    let mut result = self.0;
    
    result[1] += result[0] >> 51;
    result[0] &= Self::MASK_51;
    result[2] += result[1] >> 51;
    result[1] &= Self::MASK_51;
    result[3] += result[2] >> 51;
    result[2] &= Self::MASK_51;
    result[4] += result[3] >> 51;
    result[3] &= Self::MASK_51;
    
    Self(result)
  }

  /*
  This is the pillar of utility for lazy reduction in modular arithmetic. Because multiplication using Barrett reduction,
  We can allow >= 2^256 limb data to exist within the 13 bits of headroom in each of the five limbs indefinitely.
  This allows operations to be chained within reason, while deferring the reduction overhead to consolidated critical points.

  This takes care and deliberation, and I have culled as many reductions as I can to allow for safe chaining in the point arithmetic,
  without breaking tests. The crate tests have been spammed as a sanity check, with no issues seen.

  Do note that since the switch to Barrett in the final stages of development, modular reduction in the mul method is basically free.
  This allows for even more aggressive inline chaining, which took performance to the next level alongside other optimizations in the point
  math.

  Concepts here were studied from Curve25519-dalek's field types, with novel carry propogation precision & customs being created for Helioselene
  Prime.
  */

  pub fn reduce_weak(self) -> Self {
    let mut limbs = self.0;

    let c0 = limbs[0] >> 51;
    let c1 = limbs[1] >> 51;
    let c2 = limbs[2] >> 51;
    let c3 = limbs[3] >> 51;
    let c4 = limbs[4] >> 51;

    limbs[0] &= Self::MASK_51;
    limbs[1] &= Self::MASK_51;
    limbs[2] &= Self::MASK_51;
    limbs[3] &= Self::MASK_51;
    limbs[4] &= Self::MASK_51;

    let c4_256 = U256H::from_u64(c4);
    let c_256 = U256H::from_u128(C_1X);
    let product = c4_256.wrapping_mul(&c_256);
    
    let mask51_256 = U256H::from_u64(Self::MASK_51);
    let lo51 = (product & mask51_256).as_limbs()[0].0;
    let mi51 = ((product >> 51) & mask51_256).as_limbs()[0].0;
    let hi = (product >> 102).as_limbs()[0].0;
    
    limbs[0] += lo51;
    limbs[1] += mi51;
    limbs[2] += hi;
    
    limbs[1] += c0;
    limbs[2] += c1;
    limbs[3] += c2;
    limbs[4] += c3;
    
    let fc0 = limbs[0] >> 51;
    limbs[0] &= Self::MASK_51;
    limbs[1] += fc0;
    
    let fc1 = limbs[1] >> 51;
    limbs[1] &= Self::MASK_51;
    limbs[2] += fc1;

    Self(limbs)
  }

  /*
  Completes the deffered modular reduction using the reduction constant (C where 2^255 - C = Prime), resulting
  in an end value that will always be less than prime. This is done at comparison time for the evaluation of
  multiple limbs51 objects, OR, in a hypothetical case where a U256 must be extracted from an instance for use
  in other forms of arithmetic.

  Due to the large C for Helioselene compared to Field25519 where C is only 19, a new term breakdown and carry
  propogation approach was needed when compared to what you'd see in something like curve25519-dalek.
  */

  pub fn reduce_canonical(&self) -> Self {
    let reduced = self.reduce_weak();
    let mut result = [
      reduced.0[0],
      reduced.0[1],
      reduced.0[2],
      reduced.0[3],
      reduced.0[4],
    ];
    
    let mut limbs_u256 = [
      U256H::from_u64(result[0]),
      U256H::from_u64(result[1]),
      U256H::from_u64(result[2]),
      U256H::from_u64(result[3]),
      U256H::from_u64(result[4]),
    ];
    
    let c_256 = U256H::from_u128(C_1X);
    let mask51 = U256H::from_u64(Self::MASK_51);
    
    let mut q = limbs_u256[0].add_truncate(&c_256) >> 51;
    q = limbs_u256[1].add_truncate(&q) >> 51;
    q = limbs_u256[2].add_truncate(&q) >> 51;
    q = limbs_u256[3].add_truncate(&q) >> 51;
    q = limbs_u256[4].add_truncate(&q) >> 51;
    
    let q_product = q.wrapping_mul(&c_256);
    let q_lo51 = q_product & mask51;
    let q_mi51 = (q_product >> 51) & mask51;
    let q_hi = q_product >> 102;
    
    limbs_u256[0] = limbs_u256[0].add_truncate(&q_lo51);
    limbs_u256[1] = limbs_u256[1].add_truncate(&q_mi51);
    limbs_u256[2] = limbs_u256[2].add_truncate(&q_hi);
    
    result[0] = limbs_u256[0].low_u64();
    result[1] = limbs_u256[1].low_u64();
    result[2] = limbs_u256[2].low_u64();
    result[3] = limbs_u256[3].low_u64();
    result[4] = limbs_u256[4].low_u64();
    
    result[1] += result[0] >> 51;
    result[0] &= Self::MASK_51;
    result[2] += result[1] >> 51;
    result[1] &= Self::MASK_51;
    result[3] += result[2] >> 51;
    result[2] &= Self::MASK_51;
    result[4] += result[3] >> 51;
    result[3] &= Self::MASK_51;
    result[4] &= Self::MASK_51;

    Self(result)
  }

  /*
  Spits out the canonical representation of a Limbs51 object as bytes.
  */

  pub fn to_bytes(&self) -> [u8; 32] {
    let l = self.reduce_canonical();
    
    let r0 = l.0[0];
    let r1 = l.0[1];
    let r2 = l.0[2];
    let r3 = l.0[3];
    let r4 = l.0[4];

    let mut s = [0u8; 32];
    s[0] = r0 as u8;
    s[1] = (r0 >> 8) as u8;
    s[2] = (r0 >> 16) as u8;
    s[3] = (r0 >> 24) as u8;
    s[4] = (r0 >> 32) as u8;
    s[5] = (r0 >> 40) as u8;
    s[6] = ((r0 >> 48) | (r1 << 3)) as u8;
    s[7] = (r1 >> 5) as u8;
    s[8] = (r1 >> 13) as u8;
    s[9] = (r1 >> 21) as u8;
    s[10] = (r1 >> 29) as u8;
    s[11] = (r1 >> 37) as u8;
    s[12] = ((r1 >> 45) | (r2 << 6)) as u8;
    s[13] = (r2 >> 2) as u8;
    s[14] = (r2 >> 10) as u8;
    s[15] = (r2 >> 18) as u8;
    s[16] = (r2 >> 26) as u8;
    s[17] = (r2 >> 34) as u8;
    s[18] = (r2 >> 42) as u8;
    s[19] = ((r2 >> 50) | (r3 << 1)) as u8;
    s[20] = (r3 >> 7) as u8;
    s[21] = (r3 >> 15) as u8;
    s[22] = (r3 >> 23) as u8;
    s[23] = (r3 >> 31) as u8;
    s[24] = (r3 >> 39) as u8;
    s[25] = ((r3 >> 47) | (r4 << 4)) as u8;
    s[26] = (r4 >> 4) as u8;
    s[27] = (r4 >> 12) as u8;
    s[28] = (r4 >> 20) as u8;
    s[29] = (r4 >> 28) as u8;
    s[30] = (r4 >> 36) as u8;
    s[31] = (r4 >> 44) as u8;

    s
  }

  pub fn ct_eq(&self, other: &Self) -> Choice {
    let self_bytes = self.to_bytes();
    let other_bytes = other.to_bytes();

    self_bytes.ct_eq(&other_bytes)
  }

  pub fn ct_lt(&self, other: &Self) -> Choice {
    let mut borrow = 0u64;
    
    for i in 0..5 {
      let (_diff, b) = self.0[i].overflowing_sub(other.0[i].wrapping_add(borrow));
      borrow = b as u64;
    }
    
    Choice::from(borrow as u8)
  }

  pub fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self([
      u64::conditional_select(&a.0[0], &b.0[0], choice),
      u64::conditional_select(&a.0[1], &b.0[1], choice),
      u64::conditional_select(&a.0[2], &b.0[2], choice),
      u64::conditional_select(&a.0[3], &b.0[3], choice),
      u64::conditional_select(&a.0[4], &b.0[4], choice),
    ])
  }

  // Underflow-safe negation of Limbs51 objects, provided they aren't themselves bigger than 276 bits
  pub fn negate(&mut self) {
    *self = Self([
      Self::P_MUL[0] - self.0[0],
      Self::P_MUL[1] - self.0[1],
      Self::P_MUL[2] - self.0[2],
      Self::P_MUL[3] - self.0[3],
      Self::P_MUL[4] - self.0[4],
    ])
  }

  pub fn is_odd(&self) -> Choice {
    let bytes = self.to_bytes();
    (bytes[0] & 1).into()
  }

  // Add limbs assuming there is enough headroom for the result without overflow. This can be ensured by
  // management in the Point math, allowing for the avoidance of redundant reduction overhead.
  #[inline(always)]
  pub fn add_lazy(self, other: Limbs51) -> Limbs51 {
    Self([
      self.0[0] + other.0[0],
      self.0[1] + other.0[1],
      self.0[2] + other.0[2],
      self.0[3] + other.0[3],
      self.0[4] + other.0[4],
    ])
  }

  // Underflow-safe subtraction of Limbs51 objects, provided other isn't bigger than 55-bit max limbs - 16 * prime + self
  #[inline(always)]
  pub fn sub_lazy(self, other: Self) -> Self {
    Self([
      self.0[0] + Self::P_MUL[0] - other.0[0],
      self.0[1] + Self::P_MUL[1] - other.0[1],
      self.0[2] + Self::P_MUL[2] - other.0[2],
      self.0[3] + Self::P_MUL[3] - other.0[3],
      self.0[4] + Self::P_MUL[4] - other.0[4],
    ])
  }
}

impl Neg for &Limbs51 {
  type Output = Limbs51;
  fn neg(self) -> Limbs51 {
    let mut output = *self;
    output.negate();
    output
  }
}

// All ops managed to be lazy reduction compatible in real use with the necessary point math
impl Add for Limbs51 {
  type Output = Limbs51;
  
  #[inline(always)]
  fn add(self, other: Limbs51) -> Limbs51 {
    self.add_lazy(other)
  }
}

impl Sub for Limbs51 {
  type Output = Self;
  
  #[inline(always)]
  fn sub(self, other: Self) -> Self {
    self.sub_lazy(other)
  }
}

impl Mul for Limbs51 {
  type Output = Self;
  
  #[inline(always)]
  fn mul(self, rhs: Self) -> Self {
    self.mul_barrett(&rhs)
  }    
}

// ====================================================================

impl_modulus!(HelioseleneQ, U256, MODULUS_STR);
type HelioseleneResidueType = Residue<HelioseleneQ, { HelioseleneQ::LIMBS }>;

/// The field novel to Helios/Selene.
#[derive(Clone, Copy, Default, Debug)]
#[repr(C)]
pub struct HelioseleneField(pub(crate) Limbs51);

pub(crate) const MODULUS: U256 = U256::from_be_hex(MODULUS_STR);
const WIDE_MODULUS: U512 = U512::from_be_hex(concat!(
  "0000000000000000000000000000000000000000000000000000000000000000",
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f",
));

field!(
  HelioseleneField,
  HelioseleneResidueType,
  MODULUS_STR,
  MODULUS,
  WIDE_MODULUS,
  5,
  1,
  "3fffffffffffffffffffffffffffffffdfbfbc165bb2b5ac375b69393c93e3d0",
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e",
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e",
  "0000000000000000000000000000000000000000000000000000000000000019",
);

impl HelioseleneField {
  pub fn wide_reduce(bytes: [u8; 64]) -> HelioseleneField {
    HelioseleneField::from_u256(HelioseleneField::reduce(U512::from_le_slice(bytes.as_ref())).into())
  }

  fn reduce(x: U512) -> U256 {
    U256::from_le_slice(&x.rem(&NonZero::new(WIDE_MODULUS).unwrap()).to_le_bytes()[.. 32])
  }

  #[inline(always)]
  pub fn reduce_narrow(x: U256) -> U256 {
    let (reduced, borrow) = x.sbb(&MODULUS, Limb::ZERO);
    U256::conditional_select(&x, &reduced, Choice::from(u8_from_bool(&mut (borrow.0 == 0))))
  }

  pub fn from_be_hex(hex: &str) -> Self {
    Self::from_u256(U256H::from_be_hex(hex))
  }

  pub fn reduce_canonical(&self) -> Self {
    Self(self.0.reduce_canonical())
  }
  
  pub fn is_odd(&self) -> Choice {
    self.0.is_odd()
  }
}

impl Field for HelioseleneField {
  const ZERO: Self = Self(Limbs51::ZERO);
  const ONE: Self = Self(Limbs51::ONE);

  fn random(mut rng: impl RngCore) -> Self {
    let mut bytes = [0; 64];
    rng.fill_bytes(&mut bytes);
    Self::from_u256(Self::reduce(U512::from_le_slice(bytes.as_ref())).into())
  }

  fn square(&self) -> Self {
    Self(self.0.square())
  }

  fn double(&self) -> Self {
    (*self + self).reduce_weak()
  }

  // Constant time Binary GCD, converting to/from U256H for the computation
  #[inline(always)]
  fn invert(&self) -> CtOption<Self> {
    let reduced = self.0.reduce_weak();
    let x_4x64 = reduced.to_4x64();
    let x = U256H { limbs: x_4x64 };
    
    const P_LIMBS: [u64; 4] = [
      0x6eb6d2727927c79f,
      0xbf7f782cb7656b58,
      0xffffffffffffffff,
      0x7fffffffffffffff
    ];
    let p = U256H { limbs: P_LIMBS };
    
    let mut a = x;
    let mut b = p;
    let mut u = U256H::from_u64(1);
    let mut v = U256H::from_u64(0);
    
    for _ in 0..510 {
      let a_odd = a.limbs[0] & 1;
      let a_lt_b = a.ct_lt(&b);
      let swap = a_odd & a_lt_b;
      
      U256H::conditional_swap(&mut a, &mut b, swap);
      U256H::conditional_swap(&mut u, &mut v, swap);
      
      let mask_odd = 0u64.wrapping_sub(a_odd);
      // Subtract (b & mask_odd) - so we subtract b if odd, 0 if even
      a = a.sub(&U256H {
        limbs: [
          b.limbs[0] & mask_odd,
          b.limbs[1] & mask_odd,
          b.limbs[2] & mask_odd,
          b.limbs[3] & mask_odd,
        ]
      });
      
      // For u: subtract (v & mask_odd)
      let u_lt_v = u.ct_lt(&v);
      let needs_p = mask_odd & 0u64.wrapping_sub(u_lt_v);

      u = u.sub(&U256H {
        limbs: [
          v.limbs[0] & mask_odd,
          v.limbs[1] & mask_odd,
          v.limbs[2] & mask_odd,
          v.limbs[3] & mask_odd,
        ]
      }).add_truncate(&U256H {
        limbs: [
          P_LIMBS[0] & needs_p,
          P_LIMBS[1] & needs_p,
          P_LIMBS[2] & needs_p,
          P_LIMBS[3] & needs_p,
        ]
      });
      
      // Division by 2
      a = a.shr(1);
      
      // u division with masking
      let u_odd = u.limbs[0] & 1;
      let mask = 0u64.wrapping_sub(u_odd);
      
      u = u.add_truncate(&U256H {
        limbs: [
          P_LIMBS[0] & mask,
          P_LIMBS[1] & mask,
          P_LIMBS[2] & mask,
          P_LIMBS[3] & mask,
        ]
      });
      u = u.shr(1);
    }
    
    let mut is_one = (b.limbs[0] == 1) & 
                 (b.limbs[1] == 0) & 
                 (b.limbs[2] == 0) & 
                 (b.limbs[3] == 0);
    
    let v_5x51 = Limbs51::from_4x64_to_5x51(&v.limbs);
    let result = Self(v_5x51);
    CtOption::new(result, Choice::from(u8_from_bool(&mut is_one)))
  }

  /*
  Constant time sqrt using Tonelli–Shanks Algorithm with a precomputed exponent constant. An addition chain that allows
  term re-use for the repeating ones found in SQRT_EXP_BYTES was derived to allow a more efficient process than
  simply using the pow (see backend.rs) sliding window technique across the entire byte set. Significant performance
  gains and cycle count reductions were enabled by this.

  The operation should be constant time even without forcefully reading the whole table[] every iteration,
  because SQRT_EXP_BYTES never changes.
  */

  fn sqrt(&self) -> CtOption<Self> {
    const SQRT_EXP_BYTES: [u8; 32] = [
      0xe8, 0xf1, 0x49, 0x9e, 0x9c, 0xb4, 0xad, 0x1b,
      0xd6, 0x5a, 0xd9, 0x2d, 0x0b, 0xde, 0xdf, 0xef,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x1f,
    ];
    
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
    
    res *= table[1];
    
    res = res.square().square().square().square();
    res *= table[15];
    
    let self_255 = {
      let mut r = table[15];
      r = r.square().square().square().square() * &table[15];
      r
    };

    let self_4095 = {
      let mut r = self_255;
      r = r.square().square().square().square() * &table[15];
      r
    };

    for _ in 0..10 {
      res = res.square().square().square().square().square().square()
        .square().square().square().square().square().square();
      res *= &self_4095;
    }

    for window in (0..32).rev() {
      res = res.square().square().square().square();
      
      let bit_offset = window * 4;
      let mut bits = 0u8;
      bits |= (SQRT_EXP_BYTES[bit_offset / 8] >> (bit_offset % 8)) & 1;
      bits |= ((SQRT_EXP_BYTES[(bit_offset + 1) / 8] >> ((bit_offset + 1) % 8)) & 1) << 1;
      bits |= ((SQRT_EXP_BYTES[(bit_offset + 2) / 8] >> ((bit_offset + 2) % 8)) & 1) << 2;
      bits |= ((SQRT_EXP_BYTES[(bit_offset + 3) / 8] >> ((bit_offset + 3) % 8)) & 1) << 3;
      
      res *= table[bits as usize];
      
      bits.zeroize();
    }

    CtOption::new(res, res.square().ct_eq(self))
  }

  // Naive sqrt ratio that uses multiplication by inverse to simulate division.
  fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
    let div_inv_opt = div.invert();
    let div_inv = div_inv_opt.unwrap_or(Self::ZERO);
    let div_is_nonzero = div_inv_opt.is_some();
    
    let ratio = *num * div_inv;
    
    let sqrt_opt = ratio.sqrt();
    let sqrt_val = sqrt_opt.unwrap_or(Self::ZERO);
    let sqrt_exists = sqrt_opt.is_some();
    
    let is_valid = div_is_nonzero & sqrt_exists;
    
    (is_valid, sqrt_val)
  }
}

impl PartialEq for HelioseleneField {
  fn eq(&self, other: &Self) -> bool {
    self.0.ct_eq(&other.0).into()
  }
}
impl Eq for HelioseleneField {}

use crate::Field25519;

// Interface to allow the curve! macro to be unified despite the extra features in Helioselene.
// Redirects to faster sqrt for Helios decompression exclusively, without touching Field25519 internals.
pub trait FieldExtensions: Sized {
  fn reduce_weak(&self) -> Self;
  fn reduce_canonical(&self) -> Self;
  fn propogate_carries(&self) -> Self;
  
  /// Square k times
  fn pow2k(&self, k: usize) -> Self;
  
  /// Optimized square root
  fn sqrt_fast(&self) -> CtOption<Self>;
}

impl FieldExtensions for Field25519 {
  fn reduce_weak(&self) -> Self {
    *self
  }

  fn reduce_canonical(&self) -> Self {
    *self
  }

  fn propogate_carries(&self) -> Self {
    *self
  }
  
  #[inline]
  fn pow2k(&self, k: usize) -> Self {
    let mut res = *self;
    for _ in 0..k {
      res = res.square();
    }
    res
  }
  
  /*
  Fast sqrt for Curve 25519, with the addition chain for the inverse exponent's pattern constructed entirely inline.
  The extreme amount of repeating ones makes any sliding window unuseful, allowing for a more hardcore version
  of Helioselene sqrt to be used here for full exploitation of the mathematical traits of this curve.
  */
  fn sqrt_fast(&self) -> CtOption<Self> {
    // Precomputed sqrt(-1) = 2^((p-1)/4) mod p
    const SQRT_MINUS_ONE: Field25519 = Field25519(Residue::new(&U256::from_be_hex(
      "2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0"
    )));
    
    // Compute self^7 and self^15 directly
    let self_2 = self.square();                    // self^2
    let self_3 = self_2 * self;                    // self^3
    let self_4 = self_2.square();                  // self^4
    let self_7 = self_4 * &self_3;                 // self^7
    let self_8 = self_4.square();                  // self^8
    let self_15 = self_8 * &self_7;                // self^15
        
    // self^255 = self^(2^8 - 1) = (self^15)^16 * self^15
    let self_255 = {
      let mut r = self_15;
      r = r.square().square().square().square();
      r * &self_15
    };
    
    // self^65535 = self^(2^16 - 1) = (self^255)^256 * self^255
    let self_65535 = {
      let mut r = self_255;
      for _ in 0..8 {
        r = r.square();
      }
      r * &self_255
    };
    
    // self^(2^32 - 1) = (self^65535)^65536 * self^65535
    let self_2_32_minus_1 = {
      let mut r = self_65535;
      for _ in 0..16 {
        r = r.square();
      }
      r * &self_65535
    };
    
    // self^(2^64 - 1) = (self^(2^32-1))^(2^32) * self^(2^32-1)
    let self_2_64_minus_1 = {
      let mut r = self_2_32_minus_1;
      for _ in 0..32 {
        r = r.square();
      }
      r * &self_2_32_minus_1
    };
    
    // self^(2^128 - 1) = (self^(2^64-1))^(2^64) * self^(2^64-1)
    let self_2_128_minus_1 = {
      let mut r = self_2_64_minus_1;
      for _ in 0..64 {
        r = r.square();
      }
      r * &self_2_64_minus_1
    };
    
    // Now build self^(2^251 - 1)
    // 251 = 128 + 64 + 32 + 16 + 8 + 3
    
    let mut res = self_2_128_minus_1;
    
    // Shift left 64 and multiply by self^(2^64 - 1)
    for _ in 0..64 {
      res = res.square();
    }
    res *= &self_2_64_minus_1;
    
    // Shift left 32 and multiply by self^(2^32 - 1)
    for _ in 0..32 {
      res = res.square();
    }
    res *= &self_2_32_minus_1;
    
    // Shift left 16 and multiply by self^(2^16 - 1)
    for _ in 0..16 {
      res = res.square();
    }
    res *= &self_65535;
    
    // Shift left 8 and multiply by self^(2^8 - 1)
    for _ in 0..8 {
      res = res.square();
    }
    res *= &self_255;
    
    // Shift left 3 and multiply by self^(2^3 - 1) = self^7
    res = res.square().square().square();
    res *= &self_7;
    
    res = res.square();
    
    let r_squared = res.square();
    let is_root = r_squared.ct_eq(self);
    let neg_self = -*self;
    let is_neg_root = r_squared.ct_eq(&neg_self);
    
    let corrected_r = Self::conditional_select(
      &res,
      &(res * SQRT_MINUS_ONE),
      is_neg_root
    );
    
    CtOption::new(corrected_r, is_root | is_neg_root)
  }
}

#[test]
fn test_helioselene_field() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut rand_core::OsRng);
}