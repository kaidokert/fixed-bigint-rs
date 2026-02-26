//! Fused multiply-accumulate row operations.
//!
//! Provides row-level fused multiply-accumulate operations for
//! implementing Montgomery multiplication (CIOS, SOS, or other variants)
//! in higher-level crates. The trait abstracts over the internal limb
//! layout so callers never touch raw word arrays.

/// Row-level fused multiply-accumulate operations for big-integer types.
///
/// Implementors provide scalar × bigint accumulate/shift primitives.
/// A higher-level crate (e.g. modmath) orchestrates the outer loop of
/// a Montgomery multiplication variant using only these methods, without
/// knowledge of the internal representation.
pub trait MulAccOps: Sized + Copy + Default + crate::const_numtraits::ConstZero {
    /// The machine-word type used as a scalar in row operations.
    type Word: Copy
        + crate::const_numtraits::ConstZero
        + crate::const_numtraits::ConstOne
        + PartialOrd;

    /// Number of words in this type.
    fn word_count() -> usize;

    /// Access the `i`-th word (little-endian, `i = 0` is least significant).
    /// Returns `None` if `i >= Self::word_count()`.
    fn get_word(&self, i: usize) -> Option<Self::Word>;

    /// **Phase 1 row**: `acc += scalar * multiplicand`
    ///
    /// Iterates over all words, performing fused multiply-accumulate with
    /// incoming `carry_in`. Returns the carry-out word; the caller is
    /// responsible for propagating it into the overflow limbs.
    fn mul_acc_row(
        scalar: Self::Word,
        multiplicand: &Self,
        acc: &mut Self,
        carry_in: Self::Word,
    ) -> Self::Word;

    /// **Phase 2 row**: `[acc, acc_hi] = ([acc, acc_hi] + scalar * multiplicand) >> word_bits`
    ///
    /// The lowest word of the pre-shift sum is discarded (zero by CIOS
    /// construction). `acc_hi` is consumed and folded into the top of `acc`.
    /// Returns a carry word (0 or 1) representing overflow from the fold;
    /// the caller adds this to any higher overflow state.
    fn mul_acc_shift_row(
        scalar: Self::Word,
        multiplicand: &Self,
        acc: &mut Self,
        acc_hi: Self::Word,
    ) -> Self::Word;
}
