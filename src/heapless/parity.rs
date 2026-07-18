//! `const_num_traits::Parity` for `HeaplessBigInt`.
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
