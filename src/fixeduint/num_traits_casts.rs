use super::{FixedUInt, MachineWord};

use num_traits::{FromPrimitive, ToPrimitive};

impl<T: MachineWord, const N: usize> num_traits::NumCast for FixedUInt<T, N> {
    fn from<X>(arg: X) -> Option<Self>
    where
        X: ToPrimitive,
    {
        Some(Self::from_u64(arg.to_u64()?).unwrap())
    }
}

impl<T: MachineWord, const N: usize> num_traits::ToPrimitive for FixedUInt<T, N> {
    fn to_i64(&self) -> Option<i64> {
        None
    }
    fn to_u64(&self) -> Option<u64> {
        let mut ret: u64 = 0;
        let iter: usize = core::cmp::min(8 / Self::WORD_SIZE, N);
        for (word, bits) in (0..iter).map(|x| (x, x as u64 * Self::WORD_SIZE as u64 * 8)) {
            ret += T::to_u64(&self.array[word])? << bits;
        }
        Some(ret)
    }
}

impl<T: MachineWord, const N: usize> num_traits::FromPrimitive for FixedUInt<T, N> {
    fn from_i64(_: i64) -> Option<Self> {
        None
    }
    fn from_u64(input: u64) -> Option<Self> {
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
