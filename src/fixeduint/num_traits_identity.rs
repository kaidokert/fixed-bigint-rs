use super::{FixedUInt, MachineWord};

use num_traits::Zero;

impl<T: MachineWord, const N: usize> num_traits::Zero for FixedUInt<T, N> {
    fn zero() -> Self {
        Self::new()
    }
    fn is_zero(&self) -> bool {
        !self.array.iter().any(|v| !v.is_zero())
    }
}

impl<T: MachineWord, const N: usize> num_traits::One for FixedUInt<T, N> {
    fn one() -> Self {
        let mut ret = Self::zero();
        ret.array[0] = T::one();
        ret
    }
}

impl<T: MachineWord, const N: usize> num_traits::Bounded for FixedUInt<T, N> {
    fn min_value() -> Self {
        Self::zero()
    }
    fn max_value() -> Self {
        FixedUInt {
            array: [T::max_value(); N],
        }
    }
}
