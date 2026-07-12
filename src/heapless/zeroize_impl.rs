//! `zeroize::DefaultIsZeroes` for `HeaplessBigInt`.
//!
//! `Default` is the mathematical zero (all limbs zero, `len = 0`) and the
//! type is `Copy` with no `Drop`, so the all-zero bit pattern is a valid
//! `Default` — the `DefaultIsZeroes` contract. This is the marker
//! downstream secret (Ct) roles bind on (`Zeroize` follows via the
//! blanket impl), and what lets modmath's `MontStorage` satisfy its
//! `Zeroize` bound.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::Personality;

impl<T: MachineWord, const CAP: usize, P: Personality> zeroize::DefaultIsZeroes
    for HeaplessBigInt<T, CAP, P>
{
}
