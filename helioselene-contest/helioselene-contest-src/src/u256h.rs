use core::ops::{Mul, BitAnd, Shr};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct U256H {
  pub(crate) limbs: [u64; 4],
}

impl U256H {
  const ZERO: U256H = U256H {limbs: [0, 0, 0, 0] };
  
  pub const fn new(limbs: [u64; 4]) -> Self {
    Self { limbs }
  }

  pub const fn from_be_hex(hex: &str) -> Self {
    const fn hex_val(byte: u8) -> u8 {
      match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        b'A'..=b'F' => byte - b'A' + 10,
        _ => panic!("Invalid hex character"),
      }
    }

    const fn byte_from_hex(s: &str, i: usize) -> u8 {
      let b = s.as_bytes();
      (hex_val(b[i]) << 4) | hex_val(b[i + 1])
    }

    const fn build_limbs(hex: &str) -> [u64; 4] {
      if hex.len() != 64 {
        panic!("Hex string must be exactly 64 characters");
      }

      let mut limbs = [0u64; 4];
      let mut i = 0;
      while i < 4 {
        let mut limb = 0u64;
        let hex_start = 48 - i * 16;
        let mut j = 0;
        while j < 8 {
          let byte_i = hex_start + j * 2;
          let byte = byte_from_hex(hex, byte_i);
          limb = (limb << 8) | byte as u64;
          j += 1;
        }
        limbs[i] = limb;
        i += 1;
      }

      limbs
    }

    U256H {
      limbs: build_limbs(hex),
    }
  }

  #[inline(always)]
  pub const fn from_u64(val: u64) -> Self {
    U256H { limbs: [val, 0, 0, 0] }
  }
  
  #[inline(always)]
  pub const fn from_u128(val: u128) -> Self {
    U256H { 
      limbs: [val as u64, (val >> 64) as u64, 0, 0] 
    }
  }
  
  #[inline(always)]
  pub const fn low_u64(&self) -> u64 {
    self.limbs[0]
  }
  
  #[inline(always)]
  pub const fn low_u128(&self) -> u128 {
    self.limbs[0] as u128 | ((self.limbs[1] as u128) << 64)
  }

  #[inline(always)]
  pub fn as_limbs(&self) -> [(u64,); 4] {
    [
      (self.limbs[0],),
      (self.limbs[1],),
      (self.limbs[2],),
      (self.limbs[3],),
    ]
  }
  
  #[inline(always)]
  pub const fn is_zero(&self) -> bool {
    self.limbs[0] | self.limbs[1] | self.limbs[2] | self.limbs[3] == 0
  }

  #[inline(always)]
  pub fn add_truncate(&self, other: &U256H) -> U256H {
    let mut result = [0u64; 4];
    let mut carry = 0u64;
    
    let (sum0, c0) = self.limbs[0].overflowing_add(other.limbs[0]);
    result[0] = sum0;
    carry = c0 as u64;
    
    let (sum1a, c1a) = self.limbs[1].overflowing_add(other.limbs[1]);
    let (sum1b, c1b) = sum1a.overflowing_add(carry);
    result[1] = sum1b;
    carry = (c1a as u64) | (c1b as u64);
    
    let (sum2a, c2a) = self.limbs[2].overflowing_add(other.limbs[2]);
    let (sum2b, c2b) = sum2a.overflowing_add(carry);
    result[2] = sum2b;
    carry = (c2a as u64) | (c2b as u64);
    
    let (sum3a, _c3a) = self.limbs[3].overflowing_add(other.limbs[3]);
    let (sum3b, _c3b) = sum3a.overflowing_add(carry);
    result[3] = sum3b;
    
    U256H { limbs: result }
  }
  
  #[inline(always)]
  pub fn wrapping_mul(&self, other: &U256H) -> U256H {
    let mut result = [0u64; 8];
    
    for i in 0..4 {
      let mut carry = 0u128;
      for j in 0..4 {
        let product = (self.limbs[i] as u128) * (other.limbs[j] as u128);
        let sum = (result[i + j] as u128) + product + carry;
        result[i + j] = sum as u64;
        carry = sum >> 64;
      }
      if i + 4 < 8 {
        result[i + 4] = carry as u64;
      }
    }
    
    U256H { limbs: [result[0], result[1], result[2], result[3]] }
  }

  #[inline(always)]
  pub fn mul_by_u64(&self, val: u64) -> U256H {
    let mut result = [0u64; 4];
    let mut carry = 0u128;
    
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val as u128) + carry;
      result[i] = product as u64;
      carry = product >> 64;
    }
    
    U256H { limbs: result }
  }
  
  #[inline(always)]
  pub fn mul_by_u128(&self, val: u128) -> U256H {
    let val_lo = val as u64;
    let val_hi = (val >> 64) as u64;
    
    if val_hi == 0 {
      return self.mul_by_u64(val_lo);
    }
    
    let mut result = [0u64; 5];
    
    let mut carry = 0u128;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_lo as u128) + carry;
      result[i] = product as u64;
      carry = product >> 64;
    }
    result[4] = carry as u64;
    
    carry = 0u128;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_hi as u128) + carry;
      let sum = (result[i + 1] as u128) + (product as u64 as u128);
      result[i + 1] = sum as u64;
      carry = (product >> 64) + (sum >> 64);
    }
    
    U256H { limbs: [result[0], result[1], result[2], result[3]] }
  }

  #[inline(always)]
  pub fn mul_by_u128_with_overflow(&self, val: u128) -> (U256H, u64, u64) {
    let val_lo = val as u64;
    let val_hi = (val >> 64) as u64;
    
    let mut result = [0u64; 6];
    
    let mut carry = 0u128;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_lo as u128) + carry;
      result[i] = product as u64;
      carry = product >> 64;
    }
    result[4] = carry as u64;
    
    carry = 0u128;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_hi as u128) + carry;
      let sum = (result[i + 1] as u128) + (product as u64 as u128);
      result[i + 1] = sum as u64;
      carry = (product >> 64) + (sum >> 64);
    }
    result[5] = carry as u64;
    
    let low = U256H { limbs: [result[0], result[1], result[2], result[3]] };
    let overflow_lo = result[4];
    let overflow_hi = result[5];
    
    (low, overflow_lo, overflow_hi)
  }
  
  #[inline(always)]
  pub fn mul_by_u128_with_overflow_u128(&self, val: u128) -> (U256H, u128) {
    let val_lo = val as u64;
    let val_hi = (val >> 64) as u64;
    
    let mut result = [0u64; 6];
    
    let mut carry = 0u128;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_lo as u128) + carry;
      result[i] = product as u64;
      carry = product >> 64;
    }
    result[4] = carry as u64;
    
    carry = 0;
    for i in 0..4 {
      let product = (self.limbs[i] as u128) * (val_hi as u128) + carry;
      let sum = (result[i + 1] as u128) + (product as u64 as u128);
      result[i + 1] = sum as u64;
      carry = (product >> 64) + (sum >> 64);
    }
    result[5] = carry as u64;
    
    let low = U256H { limbs: [result[0], result[1], result[2], result[3]] };
    let overflow = (result[4] as u128) | ((result[5] as u128) << 64);
    
    (low, overflow)
  }

  #[inline(always)]
  pub fn from_u64_mul(a: u64, b: u64) -> Self {
    let product = (a as u128) * (b as u128);
    U256H::from_u128(product)
  }
  
  #[inline(always)]
  pub fn add_u64(self, val: u64) -> Self {
    let (sum0, carry0) = self.limbs[0].overflowing_add(val);
    
    let (sum1, carry1) = self.limbs[1].overflowing_add(carry0 as u64);
    
    let (sum2, carry2) = self.limbs[2].overflowing_add(carry1 as u64);
    
    let sum3 = self.limbs[3].wrapping_add(carry2 as u64);
    
    U256H { limbs: [sum0, sum1, sum2, sum3] }
  }

  #[inline(always)]
  pub fn add_u128(self, val: u128) -> Self {
    let val_lo = val as u64;
    let val_hi = (val >> 64) as u64;
    
    let (sum0, carry0) = self.limbs[0].overflowing_add(val_lo);
    let (sum1, carry1) = self.limbs[1].overflowing_add(val_hi);
    let sum1 = sum1.wrapping_add(carry0 as u64);
    let carry1 = (carry1 | (sum1 < self.limbs[1])) as u64;
    
    let sum2 = self.limbs[2].wrapping_add(carry1);
    let carry2 = (sum2 < self.limbs[2]) as u64;
    
    let sum3 = self.limbs[3].wrapping_add(carry2);
    
    U256H { limbs: [sum0, sum1, sum2, sum3] }
  }
  
  #[inline(always)]
  pub fn mul_add_u128(self, mul_val: u128, add_val: u128) -> Self {
    self.mul_by_u128(mul_val).add_u128(add_val)
  }

  #[inline(always)]
  pub fn shr(&self, shift: u32) -> U256H {
    if shift == 0 {
      return *self;
    }
    if shift >= 256 {
      return U256H::ZERO;
    }
    
    let word_shift = (shift / 64) as usize;
    let bit_shift = shift % 64;
    let mut result = [0u64; 4];
    
    if bit_shift == 0 {
      for i in 0..(4 - word_shift) {
        result[i] = self.limbs[i + word_shift];
      }
    } else {
      let carry_shift = 64 - bit_shift;
      for i in 0..(4 - word_shift) {
        result[i] = self.limbs[i + word_shift] >> bit_shift;
        if i + word_shift + 1 < 4 {
          result[i] |= self.limbs[i + word_shift + 1] << carry_shift;
        }
      }
    }
    
    U256H { limbs: result }
  }
  
  #[inline(always)]
  pub fn and_u64(&self, val: u64) -> u64 {
      self.limbs[0] & val
  }

  #[inline(always)]
  pub fn from_le_bytes(bytes: [u8; 32]) -> Self {
    let mut limbs = [0u64; 4];
    for i in 0..4 {
      let chunk = [
        bytes[i * 8],
        bytes[i * 8 + 1],
        bytes[i * 8 + 2],
        bytes[i * 8 + 3],
        bytes[i * 8 + 4],
        bytes[i * 8 + 5],
        bytes[i * 8 + 6],
        bytes[i * 8 + 7],
      ];
      limbs[i] = u64::from_le_bytes(chunk);
    }
    U256H { limbs }
  }
  
  #[inline(always)]
  pub fn from_be_bytes(bytes: [u8; 32]) -> Self {
    let mut limbs = [0u64; 4];
    for i in 0..4 {
      let chunk = [
        bytes[24 - i * 8 + 7],
        bytes[24 - i * 8 + 6],
        bytes[24 - i * 8 + 5],
        bytes[24 - i * 8 + 4],
        bytes[24 - i * 8 + 3],
        bytes[24 - i * 8 + 2],
        bytes[24 - i * 8 + 1],
        bytes[24 - i * 8],
      ];
      limbs[i] = u64::from_le_bytes(chunk);
    }
    U256H { limbs }
  }
  
  #[inline(always)]
  pub fn from_le_slice(bytes: &[u8]) -> Option<Self> {
    if bytes.len() != 32 {
      return None;
    }
    
    let mut arr = [0u8; 32];
    arr.copy_from_slice(bytes);
    Some(Self::from_le_bytes(arr))
  }
  
  #[inline(always)]
  pub fn from_be_slice(bytes: &[u8]) -> Option<Self> {
    if bytes.len() != 32 {
      return None;
    }
    
    let mut arr = [0u8; 32];
    arr.copy_from_slice(bytes);
    Some(Self::from_be_bytes(arr))
  }
  
  #[inline(always)]
  pub fn to_le_bytes(&self) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..4 {
      let limb_bytes = self.limbs[i].to_le_bytes();
      bytes[i * 8..(i + 1) * 8].copy_from_slice(&limb_bytes);
    }
    bytes
  }

  // To big-endian bytes
  #[inline(always)]
  pub fn to_be_bytes(&self) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for i in 0..4 {
      let limb_bytes = self.limbs[3 - i].to_be_bytes();
      bytes[i * 8..(i + 1) * 8].copy_from_slice(&limb_bytes);
    }
    bytes
  }

  #[inline(always)]
  pub fn from_u128_with_reduction(base: u128, reduction_term: u128, c_256: &U256H) -> Self {
    Self::from_u128(base).add_truncate(&c_256.mul_by_u128(reduction_term))
  }

  #[inline(always)]
  pub fn ct_lt(&self, other: &U256H) -> u64 {
    let mut borrow = 0u64;
    
    for i in 0..4 {
      let (_, b) = self.limbs[i].overflowing_sub(other.limbs[i].wrapping_add(borrow));
      borrow = b as u64;
    }
    
    borrow
  }
  
  #[inline(always)]
  pub fn ct_ge(&self, other: &U256H) -> u64 {
    let mut result = 0u64;
    let mut done = 0u64;
    
    for i in (0..4).rev() {
      let gt = ((other.limbs[i] < self.limbs[i]) as u64) & !done;
      let lt = ((self.limbs[i] < other.limbs[i]) as u64) & !done;
      result |= gt;
      done |= gt | lt;
    }
    
    let all_eq = !done;
    result | all_eq
  }

  #[inline(always)]
  pub fn sub(&self, other: &U256H) -> U256H {
    let mut result = U256H::ZERO;
    let mut borrow = 0u64;
    
    for i in 0..4 {
      let (diff, b1) = self.limbs[i].overflowing_sub(other.limbs[i]);
      let (diff, b2) = diff.overflowing_sub(borrow);
      result.limbs[i] = diff;
      borrow = (b1 | b2) as u64;
    }
    
    result
  }
  
  #[inline(always)]
  pub fn lt(&self, other: &U256H) -> bool {
    for i in (0..4).rev() {
      if self.limbs[i] < other.limbs[i] {
        return true;
      }
      if self.limbs[i] > other.limbs[i] {
        return false;
      }
    }
    false
  }
  
  #[inline(always)]
  pub fn ct_select(a: &U256H, b: &U256H, choice: u64) -> U256H {
    let mask = 0u64.wrapping_sub(choice);
    
    U256H {
      limbs: [
        (a.limbs[0] & !mask) | (b.limbs[0] & mask),
        (a.limbs[1] & !mask) | (b.limbs[1] & mask),
        (a.limbs[2] & !mask) | (b.limbs[2] & mask),
        (a.limbs[3] & !mask) | (b.limbs[3] & mask),
      ]
    }
  }
  
  #[inline(always)]
  pub fn conditional_swap(a: &mut U256H, b: &mut U256H, choice: u64) {
    let mask = 0u64.wrapping_sub(choice);
    
    for i in 0..4 {
      let diff = (a.limbs[i] ^ b.limbs[i]) & mask;
      a.limbs[i] ^= diff;
      b.limbs[i] ^= diff;
    }
  }

  #[inline(always)]
  pub fn shl(&self, shift: u32) -> U256H {
    if shift == 0 {
      return *self;
    }
    if shift >= 256 {
      return U256H::ZERO;
    }
    
    let word_shift = (shift / 64) as usize;
    let bit_shift = shift % 64;
    let mut result = [0u64; 4];
    
    if bit_shift == 0 {
      for i in word_shift..4 {
        result[i] = self.limbs[i - word_shift];
      }
    } else {
      let carry_shift = 64 - bit_shift;
      for i in word_shift..4 {
        result[i] = self.limbs[i - word_shift] << bit_shift;
        if i > word_shift {
          result[i] |= self.limbs[i - word_shift - 1] >> carry_shift;
        }
      }
    }
    
    U256H { limbs: result }
  }
}

impl BitAnd<U256H> for U256H {
  type Output = U256H;
  
  #[inline(always)]
  fn bitand(self, rhs: U256H) -> U256H {
    U256H {
      limbs: [
        self.limbs[0] & rhs.limbs[0],
        self.limbs[1] & rhs.limbs[1],
        self.limbs[2] & rhs.limbs[2],
        self.limbs[3] & rhs.limbs[3],
      ]
    }
  }
}

impl BitAnd<&U256H> for &U256H {
  type Output = U256H;
  
  #[inline(always)]
  fn bitand(self, rhs: &U256H) -> U256H {
    U256H {
      limbs: [
        self.limbs[0] & rhs.limbs[0],
        self.limbs[1] & rhs.limbs[1],
        self.limbs[2] & rhs.limbs[2],
        self.limbs[3] & rhs.limbs[3],
      ]
    }
  }
}

impl Shr<u32> for &U256H {
  type Output = U256H;
  
  #[inline(always)]
  fn shr(self, shift: u32) -> U256H {
    if shift == 0 {
      return *self;
    }
    if shift >= 256 {
      return U256H::ZERO;
    }
    
    let word_shift = (shift / 64) as usize;
    let bit_shift = shift % 64;
    let mut result = [0u64; 4];
    
    if bit_shift == 0 {
      for i in 0..(4 - word_shift) {
        result[i] = self.limbs[i + word_shift];
      }
    } else {
      let carry_shift = 64 - bit_shift;
      for i in 0..(4 - word_shift) {
        result[i] = self.limbs[i + word_shift] >> bit_shift;
        if i + word_shift + 1 < 4 {
          result[i] |= self.limbs[i + word_shift + 1] << carry_shift;
        }
      }
    }
    
    U256H { limbs: result }
  }
}

impl Shr<u32> for U256H {
  type Output = U256H;
  
  #[inline(always)]
  fn shr(self, shift: u32) -> U256H {
    (&self).shr(shift)
  }
}

impl Mul<&U256H> for &U256H {
  type Output = U256H;
  
  #[inline(always)]
  fn mul(self, rhs: &U256H) -> U256H {
    self.wrapping_mul(rhs)
  }
}

use crypto_bigint::U256;
use crypto_bigint::Encoding;

impl From<U256H> for U256 {
  fn from(value: U256H) -> Self {
    let mut bytes = [0u8; 32];
    for i in 0..4 {
      let limb_bytes = value.limbs[i].to_be_bytes();
      bytes[i * 8..(i + 1) * 8].copy_from_slice(&limb_bytes);
    }
    U256::from_be_slice(&bytes)
  }
}

impl From<U256> for U256H {
  fn from(value: U256) -> Self {
    let bytes = value.to_le_bytes();

    let mut limbs = [0u64; 4];
    for i in 0..4 {
      let chunk = [
        bytes[i * 8],
        bytes[i * 8 + 1],
        bytes[i * 8 + 2],
        bytes[i * 8 + 3],
        bytes[i * 8 + 4],
        bytes[i * 8 + 5],
        bytes[i * 8 + 6],
        bytes[i * 8 + 7],
      ];
      limbs[i] = u64::from_le_bytes(chunk);
    }

    U256H { limbs }
  }
}