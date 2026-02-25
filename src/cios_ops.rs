//! CIOS (Coarsely Integrated Operand Scanning) support trait.
//!
//! Provides row-level fused multiply-accumulate operations for
//! implementing CIOS Montgomery multiplication in higher-level crates.
//! The trait abstracts over the internal limb layout so callers
//! never touch raw word arrays.

/// Row-level operations for CIOS Montgomery multiplication.
///
/// Implementors provide fused scalar × bigint accumulate/shift primitives.
/// A higher-level crate (e.g. modmath) orchestrates the CIOS outer loop
/// using only these methods, without knowledge of the internal representation.
pub trait CiosOps: Sized + Copy {
    /// The machine-word type used as a scalar in row operations.
    type Word: Copy
        + num_traits::Zero
        + num_traits::One
        + num_traits::WrappingMul
        + num_traits::ops::overflowing::OverflowingAdd
        + PartialOrd
        + core::ops::Add<Output = Self::Word>;

    /// Number of words in this type.
    fn word_count() -> usize;

    /// Access the `i`-th word (little-endian, `i = 0` is least significant).
    fn word(&self, i: usize) -> Self::Word;

    /// Shorthand for `self.word(0)`.
    fn lowest_word(&self) -> Self::Word;

    /// Construct a zero-initialized value (accumulator init).
    fn zero_value() -> Self;

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

    /// Conditional subtraction: if `overflow > 0 || acc >= modulus`,
    /// replace `acc` with `acc − modulus`.
    fn conditional_sub(acc: &mut Self, modulus: &Self, overflow: Self::Word);
}
