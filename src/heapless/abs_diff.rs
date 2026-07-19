//! `const_num_traits::AbsDiff` for `HeaplessBigInt<_, Nct>`.
//!
//! `|a - b|` = the larger minus the smaller. Nct-only: the branch on the
//! comparison isn't constant-time (FixedUInt's Ct arm uses a branchless
//! select; heapless keeps its Ct trait surface minimal).

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::{AbsDiff, Nct};

impl<T, const CAP: usize> AbsDiff for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn abs_diff(self, other: Self) -> Self {
        if self >= other {
            self - other
        } else {
            other - self
        }
    }
}
