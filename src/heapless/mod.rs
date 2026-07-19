//! Unsigned integer whose width is chosen at runtime, not by the type.
//!
//! A [`HeaplessBigInt<T, CAP>`](HeaplessBigInt) carried at `len = k` **is** a
//! `k`-word integer and behaves bit-for-bit like
//! [`FixedUInt<T, k>`](crate::FixedUInt): arithmetic wraps, `<<` truncates, and
//! overflow is reported at the value's width — it is *not* a growable bignum.
//! The only difference from `FixedUInt` is that the width is `len`, a runtime
//! (public) shape parameter, rather than the const `N`. You pick `len` at
//! construction the way you pick `N`; `CAP` is only the storage ceiling
//! (`len <= CAP`), invisible to arithmetic. Every op iterates `0..self.len`,
//! never `0..CAP`. Same `Personality` typestate (`Nct` / `Ct`) and
//! `T: MachineWord` bound as `FixedUInt`.
//!
//! Because the width is `len`, a value must be *constructed* at its intended
//! width: `zero()` / `one()` / short decodes are minimal-width, so anywhere the
//! operating width matters (accumulators, field elements, reduction targets)
//! pin it from a witness with
//! [`WithPrecision`](const_num_traits::WithPrecision) — e.g.
//! `zero_with_precision_of(&modulus)` — rather than seeding from an identity
//! and letting it silently run narrow.
//!
//! # Width contract
//!
//! Every operation resolves at the *value* width `len·word_bits` and returns
//! bit-for-bit what the same-width `FixedUInt` would — no op grows past
//! `max(operand len)` or narrows the magnitude, and `CAP` never enters a
//! result. The result `len` of each op:
//!
//! | operation | result `len` |
//! |---|---|
//! | `wrapping`/`overflowing`/`checked` `add`·`sub`·`mul`, `+` `-` `*` | `max(a.len, b.len)` |
//! | `Shl` (`<<`) | `self.len` — high bits past the width are discarded |
//! | `Shr` (`>>`) | `self.len` minus the whole-word shift |
//! | `WideMul` / [`CarryingMul`](const_num_traits::CarryingMul) | `lo` and `hi` each `max(a.len, b.len)`; reconstruct `hi·2^(W·word_bits) + lo` |
//! | `Div` (`/`), `Rem` (`%`) | `max(dividend.len, divisor.len)` |
//! | `BitAnd` (`&`), `BitOr`, `BitXor` | `max(a.len, b.len)` |
//! | [`widened`](HeaplessBigInt::widened) / `WithPrecision` | the requested width (grow-only) |
//!
//! ## Construction & serialization widths
//!
//! Constructors and byte I/O carry *different* widths for the same value —
//! there is no single "natural" one for a runtime carrier. When the width
//! matters, pick the row you mean, or pin afterward with `WithPrecision`:
//!
//! | path | width |
//! |---|---|
//! | `From<u8/u16/u32>` | `ceil(size_of::<uN>() / word)` — the source int's width |
//! | inherent [`from_le_bytes`](HeaplessBigInt::from_le_bytes) / `from_be_bytes(&[u8])` | `ceil(slice.len() / word)` — the slice width |
//! | [`new_zero_with_len`](HeaplessBigInt::new_zero_with_len) / [`from_limbs`](HeaplessBigInt::from_limbs) | exactly the given `len` |
//! | `FromBytes` **trait** (`BytesHolder<T, CAP>`) | **`CAP`** — an owned holder can't be runtime-sized |
//! | inherent [`to_le_bytes`](HeaplessBigInt::to_le_bytes) / `to_be_bytes(&mut [u8])` | value width (`len·word` bytes) |
//! | `ToBytes` **trait** (`BytesHolder<T, CAP>`) | **`CAP`** — same reason |
//!
//! The trait (`ToBytes`/`FromBytes`) paths are capacity-width because their
//! owned `Bytes` associated type is fixed-size — the intended shape for a
//! full-precision operand (a modulus with `len == CAP`) and for round-tripping
//! against `FixedUInt<T, CAP>`. For value-width bytes use the inherent methods.

use crate::MachineWord;
use const_num_traits::{Ct, Nct, Personality};
use core::marker::PhantomData;

mod arith;
mod bits;
mod bitwise;
mod bytes;
#[cfg(feature = "cios")]
mod cios;
mod cmp;
mod div_rem;
mod from_prim;
mod has_personality;
mod identities;
#[cfg(feature = "num-traits")]
mod num_traits_bridge;
mod parity;
mod pow;
mod prim_bits;
#[cfg(feature = "num-traits")]
mod prim_int;
mod shift;
mod string_conversion;
#[cfg(any(feature = "nightly", feature = "use-unsafe"))]
mod to_bytes;
#[cfg(feature = "zeroize")]
mod zeroize_impl;

/// A `len`-word unsigned integer whose width is chosen at runtime.
///
/// Behaves bit-for-bit like [`FixedUInt<T, len>`](crate::FixedUInt): every op
/// resolves at the value's width (`len·word_bits`), never a growable bignum.
/// `CAP` is the maximum limb count (compile-time storage ceiling); `len` is the
/// logical used-limb count (runtime) and the operating width — the words in
/// `[len, CAP)` do not exist for arithmetic. Invariants (enforced by the
/// module):
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

// ── Constructors (shape-setting from public parameters) ──

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Zero with a caller-supplied logical length. The `len` is treated as
    /// a public shape parameter from here on. Panics if `len > CAP`.
    #[inline]
    pub fn new_zero_with_len(len: u16) -> Self {
        let () = <Self as AssertCapFits>::CHECK;
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
    ///
    /// The tail check runs in every build, not just under `debug_assertions`:
    /// downstream arithmetic, equality, and `widened` all assume the tail is
    /// zero, so a release build that skipped it would silently promote a
    /// hidden limb into the value.
    #[inline]
    pub fn from_limbs(limbs: [T; CAP], len: u16) -> Self {
        let () = <Self as AssertCapFits>::CHECK;
        assert!((len as usize) <= CAP);
        let mut i = len as usize;
        while i < CAP {
            assert!(
                is_zero(&limbs[i]),
                "HeaplessBigInt::from_limbs: zero-tail invariant violated at index {}",
                i
            );
            i += 1;
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

    /// Return a copy carried at `new_len` words, pinning the operating
    /// width without changing the value.
    ///
    /// Arithmetic here is width-driven: a `HeaplessBigInt` at `len = k`
    /// behaves exactly like `FixedUInt<T, k>`, and every op resolves at
    /// `max(operand len)`. So a value assembled from small pieces (e.g. an
    /// accumulator seeded from [`zero`](const_num_traits::Zero::zero) then
    /// added to a one-word digit) is a *narrow* type and wraps at that
    /// narrow width. To carry it at a chosen width — the way you pick `N`
    /// for `FixedUInt` — pin it here once; subsequent ops keep that width
    /// because `max` preserves it. Widening only relabels the width: the
    /// limbs in `[len, new_len)` are already zero by the zero-tail
    /// invariant.
    ///
    /// Panics if `new_len < len` (this only widens) or `new_len > CAP`.
    #[inline]
    #[must_use]
    pub fn widened(&self, new_len: u16) -> Self {
        assert!(
            new_len >= self.len && new_len as usize <= CAP,
            "widened: new_len {new_len} must be in [len {}, CAP {CAP}]",
            self.len
        );
        let mut out = *self;
        out.len = new_len;
        out
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

// Debug is personality-split like `FixedUInt`: `Nct` prints the limbs,
// `Ct` is opaque so secret values never reach a formatter.
impl<T: MachineWord + core::fmt::Debug, const CAP: usize> core::fmt::Debug
    for HeaplessBigInt<T, CAP, Nct>
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

impl<T: MachineWord, const CAP: usize> core::fmt::Debug for HeaplessBigInt<T, CAP, Ct> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("HeaplessBigInt<…>")
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
