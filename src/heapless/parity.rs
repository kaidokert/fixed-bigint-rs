//! `const_num_traits::Parity` (and its masked-return `CtParity`) for
//! `HeaplessBigInt`.
//!
//! Parity is a single-bit inspection of the lowest limb — no full-value
//! scan. For `len == 0` (mathematical zero shape) the answer is
//! deterministically even.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{Parity, Personality};

impl<T, const CAP: usize, P: Personality> Parity for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + Parity,
{
    fn is_odd(self) -> bool {
        if self.len == 0 {
            false
        } else {
            self.limbs[0].is_odd()
        }
    }

    fn is_even(self) -> bool {
        !self.is_odd()
    }
}

// `CtParity` — masked-return parity, same subtle-predicate style as
// `CtIsZero` (cmp.rs). Uniform across personalities; `subtle`'s
// constructors aren't `const fn`, so this is a plain impl. A `len == 0`
// value is deterministically even.
impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtParity
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_is_odd(&self) -> subtle::Choice {
        if self.len == 0 {
            return subtle::Choice::from(0);
        }
        let lsb = self.limbs[0] & <T as const_num_traits::ConstOne>::ONE;
        !lsb.ct_eq(&<T as const_num_traits::ConstZero>::ZERO)
    }

    fn ct_is_even(&self) -> subtle::Choice {
        !<Self as const_num_traits::ops::ct::CtParity>::ct_is_odd(self)
    }
}

#[cfg(test)]
mod tests {
    use super::HeaplessBigInt;
    use const_num_traits::ops::ct::CtParity;

    type H = HeaplessBigInt<u8, 4>;

    #[test]
    fn ct_parity_matches_value_parity() {
        for v in [0u32, 1, 2, 3, 0xFFFF_FFFE, 0xFFFF_FFFF] {
            let h = H::from(v);
            assert_eq!(bool::from(h.ct_is_odd()), v & 1 == 1, "odd({v})");
            assert_eq!(bool::from(h.ct_is_even()), v & 1 == 0, "even({v})");
        }
    }
}
