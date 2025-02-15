use num_traits::{CheckedEuclid, Euclid};

use super::{FixedUInt, MachineWord};
use num_traits::{CheckedDiv, CheckedRem};

impl<T: MachineWord, const N: usize> Euclid for FixedUInt<T, N> {
    fn div_euclid(&self, v: &Self) -> Self {
        self / v
    }

    fn rem_euclid(&self, v: &Self) -> Self {
        self % v
    }
}

impl<T: MachineWord, const N: usize> CheckedEuclid for FixedUInt<T, N> {
    fn checked_div_euclid(&self, v: &Self) -> Option<Self> {
        self.checked_div(v)
    }

    fn checked_rem_euclid(&self, v: &Self) -> Option<Self> {
        self.checked_rem(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_euclid() {
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(a.div_euclid(&b), 3u8.into());
        assert_eq!(a.rem_euclid(&b), 10u8.into());
    }

    #[test]
    fn test_checked_div_euclid() {
        let a = FixedUInt::<u8, 2>::from(100u8);
        let b = FixedUInt::<u8, 2>::from(30u8);
        assert_eq!(a.checked_div_euclid(&b), Some(3u8.into()));
        assert_eq!(a.checked_rem_euclid(&b), Some(10u8.into()));
    }
}
