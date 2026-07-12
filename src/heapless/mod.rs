//! Fixed-capacity, runtime-length unsigned bignum.
//!
//! Sibling type to [`FixedUInt`](crate::FixedUInt). Same `Personality`
//! typestate (`Nct` / `Ct`), same `T: MachineWord` bound. The distinction:
//! `CAP` is compile-time, `len` is a runtime shape parameter treated as
//! public. Every arithmetic op iterates `0..self.len` (or
//! `0..output.len()`), not `0..CAP`.
//!
//! See `notes/HEAPLESS_BIGINT_SPEC_v3.md` for the full design record.
//!
//! **Sketch / parked.** The full trait surface, CIOS integration, and
//! CT-verify fixtures come later; this module covers the core basics
//! needed to prototype modmath arithmetic against.

use crate::MachineWord;
use const_num_traits::{Nct, Personality};
use core::marker::PhantomData;

mod arith;
mod cmp;
mod identities;
mod shift;

/// Fixed-capacity, runtime-length unsigned bignum.
///
/// `CAP` is the maximum limb count (compile-time). `len` is the logical
/// used-limb count (runtime). Invariants (enforced by the module):
///
/// - `CAP <= u16::MAX as usize` (compile-time-asserted).
/// - `(len as usize) <= CAP`.
/// - `limbs[len as usize..CAP]` is all zero at every observable state.
/// - `len` is set only from public shape parameters, never from limb content.
pub struct HeaplessBigInt<T, const CAP: usize, P: Personality = Nct>
where
    T: MachineWord,
{
    pub(crate) limbs: [T; CAP],
    pub(crate) len: u16,
    pub(crate) _p: PhantomData<P>,
}

/// Compile-time assertion that `CAP` fits in `u16` (the `len` field type).
pub(crate) trait AssertCapFits {
    const CHECK: ();
}

impl<T: MachineWord, const CAP: usize, P: Personality> AssertCapFits for HeaplessBigInt<T, CAP, P> {
    const CHECK: () = assert!(
        CAP <= u16::MAX as usize,
        "HeaplessBigInt: CAP exceeds u16::MAX; len type cannot represent this capacity"
    );
}

// ── Constructors (all Class A: shape-setting from public parameters) ──

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Zero with a caller-supplied logical length. The `len` is treated as
    /// a public shape parameter from here on. Panics if `len > CAP`.
    #[inline]
    pub fn new_zero_with_len(len: u16) -> Self {
        let _ = <Self as AssertCapFits>::CHECK;
        assert!(
            (len as usize) <= CAP,
            "HeaplessBigInt::new_zero_with_len: len {} > CAP {}",
            len,
            CAP,
        );
        Self {
            limbs: [zero::<T>(); CAP],
            len,
            _p: PhantomData,
        }
    }

    /// Full-capacity zero: `len = CAP`. Used where an algorithm needs a
    /// pre-sized workspace (CIOS accumulator, product buffer).
    #[inline]
    pub fn zero_full_cap() -> Self {
        Self::new_zero_with_len(CAP as u16)
    }

    /// Construct from a limb array + explicit `len`. Panics if `len > CAP`
    /// or if any limb at index `>= len` is non-zero (invariant check).
    #[inline]
    pub fn from_limbs(limbs: [T; CAP], len: u16) -> Self {
        let _ = <Self as AssertCapFits>::CHECK;
        assert!((len as usize) <= CAP);
        #[cfg(debug_assertions)]
        {
            let mut i = len as usize;
            while i < CAP {
                assert!(
                    is_zero(&limbs[i]),
                    "HeaplessBigInt::from_limbs: zero-tail invariant violated at index {}",
                    i
                );
                i += 1;
            }
        }
        Self {
            limbs,
            len,
            _p: PhantomData,
        }
    }
}

// ── Accessors ──

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Logical length in used limbs. Public shape parameter.
    #[inline]
    pub const fn len(&self) -> u16 {
        self.len
    }

    /// True iff `len == 0` (mathematical zero shape).
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Maximum limb count.
    #[inline]
    pub const fn capacity(&self) -> usize {
        CAP
    }

    /// Read-only view of the used limbs.
    #[inline]
    pub fn limbs(&self) -> &[T] {
        &self.limbs[..self.len as usize]
    }

    /// Full-buffer view including the zero tail. Only meaningful under
    /// the zero-tail invariant.
    #[inline]
    pub fn all_limbs(&self) -> &[T; CAP] {
        &self.limbs
    }
}

// ── Copy / Clone ──

impl<T: MachineWord, const CAP: usize, P: Personality> Clone for HeaplessBigInt<T, CAP, P> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Copy for HeaplessBigInt<T, CAP, P> {}

impl<T: MachineWord + core::fmt::Debug, const CAP: usize, P: Personality> core::fmt::Debug
    for HeaplessBigInt<T, CAP, P>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "HeaplessBigInt<{}, {}, _>{{ limbs: {:?}, len: {} }}",
            core::any::type_name::<T>(),
            CAP,
            &self.limbs[..self.len as usize],
            self.len,
        )
    }
}

// ── Internal helpers ──

#[inline]
pub(crate) fn zero<T: MachineWord>() -> T {
    <T as const_num_traits::ConstZero>::ZERO
}

#[inline]
pub(crate) fn is_zero<T: MachineWord>(v: &T) -> bool {
    <T as const_num_traits::Zero>::is_zero(v)
}
