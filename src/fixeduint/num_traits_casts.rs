use super::{FixedUInt, MachineWord};

use num_traits::{Bounded, FromPrimitive, ToPrimitive};

impl<T: MachineWord, const N: usize> num_traits::NumCast for FixedUInt<T, N> {
    fn from<X>(arg: X) -> Option<Self>
    where
        X: ToPrimitive,
    {
        Self::from_u64(arg.to_u64()?)
    }
}

impl<T: MachineWord, const N: usize> num_traits::ToPrimitive for FixedUInt<T, N> {
    fn to_i64(&self) -> Option<i64> {
        None
    }
    fn to_u64(&self) -> Option<u64> {
        let mut ret: u64 = 0;
        // Determine how many words are needed to fill a u64 (64 bits)
        // If WORD_SIZE is 4 (u32), we read 2 words. If 8 (u64), we read 1.
        let iter_limit = core::cmp::min(8 / Self::WORD_SIZE, N);

        // Overflow check: any remaining higher limbs must be zero
        for i in iter_limit..N {
            if self.array[i] != T::zero() {
                return None;
            }
        }

        for (i, word) in self.array.iter().take(iter_limit).enumerate() {
            // Convert generic T to bytes (Little Endian)
            let bytes = word.to_le_bytes();

            // Iterate over bytes and shift them into the u64 result
            for (j, &byte) in bytes.as_ref().iter().enumerate() {
                // Calculate the global bit position for this byte
                let bit_shift = (i * Self::WORD_SIZE + j) * 8;

                // Safety check: ensure we don't shift out of u64 bounds
                if bit_shift < 64 {
                    ret |= (byte as u64) << bit_shift;
                }
            }
        }

        Some(ret)
    }
}

impl<T: MachineWord, const N: usize> num_traits::FromPrimitive for FixedUInt<T, N> {
    fn from_i64(_: i64) -> Option<Self> {
        None
    }
    fn from_u64(input: u64) -> Option<Self> {
        // If max_value() fits in a u64, verify the input does not exceed it.
        // When to_u64() returns `None`, the target type is wider than 64 bits
        // and therefore any u64 value will fit.
        if let Some(max) = Self::max_value().to_u64() {
            if input > max {
                return None;
            }
        }
        Some(Self::from_le_bytes(&input.to_le_bytes()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cast<T: num_traits::NumCast + PartialEq>(a: u32, b: u8) -> bool {
        let my_a = T::from(a).unwrap();
        let my_b = T::from(b).unwrap();
        my_a == my_b
    }

    type Fixed = FixedUInt<u8, 1>;
    // Test numcast
    #[test]
    fn test_numcast() {
        assert!(cast::<Fixed>(123, 123));
        assert!(cast::<Fixed>(225, 225));
    }
}
