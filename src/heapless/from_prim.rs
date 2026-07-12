//! `From<u8>` / `From<u16>` / `From<u32>` for `HeaplessBigInt`.
//!
//! Small-value constructors. Output `len` is fixed by the source
//! primitive width (`ceil(size_of::<uN>() / size_of::<T>())`), not by
//! the value — so the shape is public. Under-sized capacity (`CAP` too
//! small to hold the source primitive) triggers `from_le_bytes`'s
//! runtime assertion; matches `FixedUInt`'s implicit contract.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::Personality;

impl<T: MachineWord, const CAP: usize, P: Personality> From<u8> for HeaplessBigInt<T, CAP, P> {
    fn from(v: u8) -> Self {
        Self::from_le_bytes(&v.to_le_bytes())
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> From<u16> for HeaplessBigInt<T, CAP, P> {
    fn from(v: u16) -> Self {
        Self::from_le_bytes(&v.to_le_bytes())
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> From<u32> for HeaplessBigInt<T, CAP, P> {
    fn from(v: u32) -> Self {
        Self::from_le_bytes(&v.to_le_bytes())
    }
}
