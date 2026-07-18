//! `From<u8>` / `From<u16>` / `From<u32>` for `HeaplessBigInt`.
//!
//! Small-value constructors. Output `len` is fixed by the source
//! primitive width (`ceil(size_of::<uN>() / size_of::<T>())`), not by
//! the value — so the shape is public. Under-sized capacity (`CAP` too
//! small to hold the source primitive) triggers `from_le_bytes`'s
//! runtime assertion; matches `FixedUInt`'s implicit contract.
//!
//! This is the source-int width, which is likely narrower than the width
//! a downstream computation needs — see the construction-width table in
//! the [module docs](super). To carry the value at a chosen width, pin it
//! with [`WithPrecision`](const_num_traits::WithPrecision) (e.g.
//! `From::from(v).widen_to_precision_of(&modulus)`).

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::Personality;

macro_rules! from_primitive {
    ($($t:ty),+) => { $(
        impl<T: MachineWord, const CAP: usize, P: Personality> From<$t> for HeaplessBigInt<T, CAP, P> {
            fn from(v: $t) -> Self {
                Self::from_le_bytes(&v.to_le_bytes())
            }
        }
    )+ };
}

from_primitive!(u8, u16, u32);
