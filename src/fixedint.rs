use core::ops::{Add, Neg, Sub};

use crate::{FixedUInt, MachineWord};

/// Very small signed counterpart to [`FixedUInt`], using two's-complement bits.
///
/// This is intentionally minimal for now: it exposes the raw bit representation
/// and a handful of wrapping arithmetic operations.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct FixedInt<T, const N: usize>
where
    T: MachineWord,
{
    bits: FixedUInt<T, N>,
}

impl<T: MachineWord, const N: usize> FixedInt<T, N> {
    const WORD_BITS: usize = core::mem::size_of::<T>() * 8;

    #[inline]
    fn assert_non_zero_words() {
        assert!(N > 0, "FixedInt requires N > 0");
    }

    /// Returns zero.
    pub fn new() -> Self {
        Self::assert_non_zero_words();
        Self {
            bits: FixedUInt::new(),
        }
    }

    /// Build from a raw two's-complement bit pattern.
    pub fn from_bits(bits: FixedUInt<T, N>) -> Self {
        Self::assert_non_zero_words();
        Self { bits }
    }

    /// Return the raw two's-complement bit pattern.
    pub fn to_bits(self) -> FixedUInt<T, N> {
        self.bits
    }

    /// Returns `true` when the sign bit is set.
    pub fn is_negative(&self) -> bool {
        let highest = self
            .bits
            .words()
            .split_last()
            .expect("FixedInt requires N > 0")
            .0;
        ((*highest >> (Self::WORD_BITS - 1)) & T::one()) == T::one()
    }

    /// Wrapping absolute value.
    pub fn abs(self) -> Self {
        if self.is_negative() {
            -self
        } else {
            self
        }
    }

    /// Temporary test utility: lossy conversion into i128 (with sign extension / truncation).
    ///
    /// This is intentionally test-only during the prototype phase.
    #[cfg(test)]
    fn to_i128(self) -> i128 {
        let mut out = if self.is_negative() {
            [0xFFu8; 16]
        } else {
            [0u8; 16]
        };
        for (word_idx, word) in self.bits.words().iter().enumerate() {
            let bytes = word.to_le_bytes();
            let start = word_idx * core::mem::size_of::<T>();
            if start >= out.len() {
                break;
            }
            let end = (start + bytes.as_ref().len()).min(out.len());
            let src_len = end - start;
            out[start..end].copy_from_slice(&bytes.as_ref()[..src_len]);
        }
        i128::from_le_bytes(out)
    }
}

impl<T: MachineWord, const N: usize> Default for FixedInt<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// Temporary test utility: allows constructing prototype values from `i128` in tests.
///
/// This is intentionally test-only during the prototype phase.
#[cfg(test)]
impl<T: MachineWord, const N: usize> From<i128> for FixedInt<T, N> {
    fn from(value: i128) -> Self {
        FixedInt::<T, N>::assert_non_zero_words();

        let mut words = *FixedUInt::<T, N>::from_le_bytes(&value.to_le_bytes()).words();

        if value < 0 {
            let word_size = core::mem::size_of::<T>();
            let i128_words = 16 / word_size;
            for word in words.iter_mut().skip(i128_words.min(N)) {
                *word = T::max_value();
            }
        }

        Self {
            bits: FixedUInt::from(words),
        }
    }
}

impl<T: MachineWord, const N: usize> Neg for FixedInt<T, N> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let one: FixedUInt<T, N> = 1u8.into();
        Self {
            bits: (!self.bits) + one,
        }
    }
}

impl<T: MachineWord, const N: usize> Add for FixedInt<T, N> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            bits: self.bits + rhs.bits,
        }
    }
}

impl<T: MachineWord, const N: usize> Sub for FixedInt<T, N> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::FixedInt;

    #[test]
    fn signed_roundtrip_i128_small() {
        let x: FixedInt<u64, 2> = (-12345_i128).into();
        assert!(x.is_negative());
        assert_eq!(x.to_i128(), -12345);
    }

    #[test]
    fn signed_wrapping_addition() {
        let a: FixedInt<u8, 1> = 120i128.into();
        let b: FixedInt<u8, 1> = 120i128.into();
        assert_eq!((a + b).to_i128(), -16);
    }

    #[test]
    #[should_panic(expected = "FixedInt requires N > 0")]
    fn zero_words_disallowed() {
        let _ = FixedInt::<u8, 0>::new();
    }
}
