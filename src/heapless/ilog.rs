//! `const_num_traits::Ilog2` / `Ilog10` / `Ilog` for `HeaplessBigInt<_, Nct>`.
//!
//! All return a plain `u32` bit/digit count, so there is no result width to
//! preserve. Nct-only: the divide-down loops and the zero/base guards branch
//! on value. `ilog2` reads the highest set bit directly (`bit_length - 1`);
//! `ilog10`/`ilog` count divide-downs like `FixedUInt`.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{CarryingMul, Ilog, Ilog2, Ilog10, Nct, Zero};

impl<T, const CAP: usize> Ilog2 for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    fn ilog2(self) -> u32 {
        match <Self as Ilog2>::checked_ilog2(self) {
            Some(v) => v,
            None => panic!("ilog2: argument is zero"),
        }
    }

    fn checked_ilog2(self) -> Option<u32> {
        if <Self as Zero>::is_zero(&self) {
            return None;
        }
        // ilog2 = position of the highest set bit = bit_length - 1.
        Some(self.bit_length() as u32 - 1)
    }
}

impl<T, const CAP: usize> Ilog10 for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn ilog10(self) -> u32 {
        match <Self as Ilog10>::checked_ilog10(self) {
            Some(v) => v,
            None => panic!("ilog10: argument is zero"),
        }
    }

    fn checked_ilog10(self) -> Option<u32> {
        if <Self as Zero>::is_zero(&self) {
            return None;
        }
        let ten: Self = From::from(10u8);
        let mut n = self;
        let mut count = 0u32;
        while n >= ten {
            n /= ten;
            count += 1;
        }
        Some(count)
    }
}

impl<T, const CAP: usize> Ilog for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn ilog(self, base: Self) -> u32 {
        match <Self as Ilog>::checked_ilog(self, base) {
            Some(v) => v,
            None => panic!("ilog: argument is zero or base is less than 2"),
        }
    }

    fn checked_ilog(self, base: Self) -> Option<u32> {
        if <Self as Zero>::is_zero(&self) {
            return None;
        }
        let two: Self = From::from(2u8);
        if base < two {
            return None;
        }
        // Route the common bases through the O(width) bit/decimal paths instead
        // of the O(width²) divide-down loop.
        if base == two {
            return <Self as Ilog2>::checked_ilog2(self);
        }
        let ten: Self = From::from(10u8);
        if base == ten {
            return <Self as Ilog10>::checked_ilog10(self);
        }
        let mut n = self;
        let mut count = 0u32;
        while n >= base {
            n /= base;
            count += 1;
        }
        Some(count)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::{Ilog, Ilog2, Ilog10};

    type H = HeaplessBigInt<u8, 2>;

    #[test]
    fn ilog2_values() {
        for (n, r) in [(1u16, 0u32), (2, 1), (3, 1), (8, 3), (255, 7), (32768, 15)] {
            assert_eq!(Ilog2::ilog2(H::from(n)), r, "ilog2({n})");
        }
        assert_eq!(Ilog2::checked_ilog2(H::from(0u8)), None);
    }

    #[test]
    fn ilog10_values() {
        for (n, r) in [(1u16, 0u32), (9, 0), (10, 1), (999, 2), (10000, 4)] {
            assert_eq!(Ilog10::ilog10(H::from(n)), r, "ilog10({n})");
        }
        assert_eq!(Ilog10::checked_ilog10(H::from(0u8)), None);
    }

    #[test]
    fn ilog_base_values() {
        assert_eq!(Ilog::ilog(H::from(27u8), H::from(3u8)), 3);
        assert_eq!(Ilog::ilog(H::from(256u16), H::from(16u8)), 2);
        // Zero argument and base < 2 are None.
        assert_eq!(Ilog::checked_ilog(H::from(0u8), H::from(2u8)), None);
        assert_eq!(Ilog::checked_ilog(H::from(10u8), H::from(1u8)), None);
    }

    // The base-2/10 fast paths must agree with both the divide-down loop and
    // the dedicated ilog2/ilog10.
    #[test]
    fn ilog_common_base_fast_paths() {
        for n in [1u16, 2, 3, 8, 255, 1024, 40000] {
            assert_eq!(
                Ilog::ilog(H::from(n), H::from(2u8)),
                Ilog2::ilog2(H::from(n)),
                "ilog(base 2, {n})"
            );
        }
        for n in [1u16, 9, 10, 99, 1000, 40000] {
            assert_eq!(
                Ilog::ilog(H::from(n), H::from(10u8)),
                Ilog10::ilog10(H::from(n)),
                "ilog(base 10, {n})"
            );
        }
    }
}
