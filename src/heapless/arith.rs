//! Add / Sub / Mul for `HeaplessBigInt`.
//!
//! Every op operates at the operands' width `max(a.len, b.len)` and
//! returns bit-for-bit what the same-width `FixedUInt` returns: a value
//! carried at `len = k` is a `k`-word integer, and the capacity beyond
//! `len` does not exist as far as arithmetic is concerned. Wrapping,
//! overflow, and carry/borrow all resolve at that width; `CAP` never
//! enters an answer.
//!
//! Loop counts derive from the public `len`s and per-limb branchless
//! primitives from `const_num_traits`, so iteration is CT-safe under the
//! "len is public" invariant regardless of Personality — the Nct and Ct
//! arms share one body.

use super::cmp::ct_select;
use super::{HeaplessBigInt, is_zero, zero};
use crate::MachineWord;
use const_num_traits::{
    BorrowingSub, Bounded, CarryingAdd, CarryingMul, CheckedAdd, CheckedMul, CheckedSub, Ct, Nct,
    OverflowingAdd, OverflowingMul, OverflowingSub, Personality, PersonalityTag, SaturatingAdd,
    SaturatingMul, SaturatingSub, WrappingAdd, WrappingMul, WrappingSub,
};
use core::marker::PhantomData;

// The checked `+`/`-`/`*` operators panic on overflow at the operands'
// width. That panic branches on a data-dependent overflow bit, so it
// runs for `Nct` only; the `Ct` arm wraps silently (like `wrapping_*`),
// keeping control flow value-independent. Mirrors `FixedUInt`'s
// `maybe_panic_if::<P>`.
// All-ones value at a given width (`len` limbs saturated). This is the
// saturation target for add/mul overflow: the max at the *operand* width
// `max(a.len, b.len)`, matching `FixedUInt<T, width>::max_value()`. It is NOT
// `Bounded::max_value()`, which on this carrier is the CAP-wide max.
#[inline]
pub(crate) fn max_at_len<T: MachineWord, const CAP: usize, P: Personality>(
    len: u16,
) -> HeaplessBigInt<T, CAP, P> {
    let mut limbs = [zero::<T>(); CAP];
    for l in &mut limbs[..len as usize] {
        *l = <T as Bounded>::max_value();
    }
    HeaplessBigInt {
        limbs,
        len,
        _p: PhantomData,
    }
}

#[inline]
fn panic_on_overflow_if_nct<P: Personality>(overflow: bool, msg: &'static str) {
    match P::TAG {
        PersonalityTag::Nct => assert!(!overflow, "{}", msg),
        PersonalityTag::Ct => {}
    }
}

// The value/mixed receiver forms of `+`/`-`/`*` are uniform pure delegation
// to the hand-written `&Self op &Self` core (which owns the panic/wrap rule).
// Trailing tokens after the method name become extra `T` bounds (`Mul` needs
// `CarryingMul`).
macro_rules! forward_arith_receivers {
    ($imp:ident, $method:ident $($bound:tt)*) => {
        impl<T: MachineWord $($bound)*, const CAP: usize, P: Personality> core::ops::$imp
            for HeaplessBigInt<T, CAP, P>
        {
            type Output = Self;
            fn $method(self, other: Self) -> Self {
                (&self).$method(&other)
            }
        }
        impl<T: MachineWord $($bound)*, const CAP: usize, P: Personality>
            core::ops::$imp<&HeaplessBigInt<T, CAP, P>> for HeaplessBigInt<T, CAP, P>
        {
            type Output = Self;
            fn $method(self, other: &Self) -> Self {
                (&self).$method(other)
            }
        }
        impl<T: MachineWord $($bound)*, const CAP: usize, P: Personality>
            core::ops::$imp<HeaplessBigInt<T, CAP, P>> for &HeaplessBigInt<T, CAP, P>
        {
            type Output = HeaplessBigInt<T, CAP, P>;
            fn $method(self, other: HeaplessBigInt<T, CAP, P>) -> HeaplessBigInt<T, CAP, P> {
                self.$method(&other)
            }
        }
    };
}

// ── Free-function slice kernels ──
//
// Take `&[T]` / `&mut [T]` so a future refactor can share them with
// `fixed-bigint`'s existing fixed-width algorithms.

/// `out[..n] = a[..n] + b[..n]`, returning the final carry-out.
/// All three slices must have length ≥ `n`. `a` / `b` beyond their
/// respective logical `len`s must be zero (zero-tail invariant).
///
/// Slicing to `..n` up front bounds-checks once; the zip loop then has no
/// per-element indexing, so the body is panic-free.
#[inline]
pub(crate) fn add_slice<T: MachineWord>(a: &[T], b: &[T], out: &mut [T], n: usize) -> bool {
    let mut carry = false;
    for ((&ai, &bi), oi) in a[..n].iter().zip(&b[..n]).zip(&mut out[..n]) {
        let (sum, c) = <T as CarryingAdd>::carrying_add(ai, bi, carry);
        *oi = sum;
        carry = c;
    }
    carry
}

/// `out[..n] = a[..n] - b[..n]`, returning the final borrow-out.
/// Same length / zero-tail preconditions as [`add_slice`].
#[inline]
pub(crate) fn sub_slice<T: MachineWord>(a: &[T], b: &[T], out: &mut [T], n: usize) -> bool {
    let mut borrow = false;
    for ((&ai, &bi), oi) in a[..n].iter().zip(&b[..n]).zip(&mut out[..n]) {
        let (diff, br) = <T as BorrowingSub>::borrowing_sub(ai, bi, borrow);
        *oi = diff;
        borrow = br;
    }
    borrow
}

/// Schoolbook `out[..out_n] += a[..a_n] * b[..b_n]`. Assumes `out` is
/// zero-initialised on entry. A partial product past `out_n` is silently
/// truncated; `wrapping_mul` passes `out_n = max(a_n, b_n)` to keep the
/// low `width` words (the high half is dropped, as at a fixed width).
///
/// `T: CarryingMul<Unsigned = T, Output = T>` is stated explicitly because
/// `MachineWord`'s supertrait chain does not include `CarryingMul` — the
/// FixedUInt path routes multiplication through the `ConstDoubleWord`
/// associated type rather than the `CarryingMul` primitive.
#[inline]
pub(crate) fn mul_slice<T: MachineWord + CarryingMul<Unsigned = T, Output = T>>(
    a: &[T],
    a_n: usize,
    b: &[T],
    b_n: usize,
    out: &mut [T],
    out_n: usize,
) {
    // Slice to the logical lengths up front: the `a[i]` / `b[j]` reads and
    // the `out[pos]` writes are then provably in bounds, so LLVM drops the
    // per-access bounds checks from the hot nested loop.
    let a = &a[..a_n];
    let b = &b[..b_n];
    let out = &mut out[..out_n];
    let mut i = 0;
    while i < a_n {
        let mut carry = zero::<T>();
        let mut j = 0;
        while j < b_n {
            let pos = i + j;
            if pos < out_n {
                let (lo, hi) = <T as CarryingMul>::carrying_mul(a[i], b[j], carry);
                let (sum, c1) = <T as CarryingAdd>::carrying_add(out[pos], lo, false);
                out[pos] = sum;
                let (new_carry, _) = <T as CarryingAdd>::carrying_add(hi, zero::<T>(), c1);
                carry = new_carry;
            }
            j += 1;
        }
        let tail = i + b_n;
        if tail < out_n {
            let (sum, _) = <T as CarryingAdd>::carrying_add(out[tail], carry, false);
            out[tail] = sum;
        }
        i += 1;
    }
}

// ── Inherent methods on HeaplessBigInt ──

impl<T: MachineWord, const CAP: usize, P: Personality> HeaplessBigInt<T, CAP, P> {
    /// Wrapping addition at the operands' width `max(a.len, b.len)`; a
    /// carry out of that width is discarded.
    pub fn wrapping_add(&self, other: &Self) -> Self {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let _carry = add_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        debug_assert!(zero_tail_ok(&out.limbs, out_len));
        out
    }

    /// Overflowing addition, at the operands' width `max(a.len, b.len)`.
    /// Returns `(sum mod 2^(width·word_bits), carry_out)` — the carry is
    /// the bit beyond the width, reported as a flag, exactly as
    /// `FixedUInt<T, width>::overflowing_add` does. Symmetric to
    /// [`overflowing_sub`](Self::overflowing_sub). Does not grow a limb.
    pub fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let carry = add_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        (out, carry)
    }

    /// Checked addition. `None` on overflow at the operands' width.
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        let (res, overflow) = self.overflowing_add(other);
        if overflow { None } else { Some(res) }
    }

    /// Wrapping subtraction at the operands' width `max(a.len, b.len)`;
    /// underflow wraps modulo `2^(max_len·WORD_BITS)`, so a value carried
    /// at a narrower width wraps at that narrower width (like `u8` vs `u32`).
    pub fn wrapping_sub(&self, other: &Self) -> Self {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let _borrow = sub_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        debug_assert!(zero_tail_ok(&out.limbs, out_len));
        out
    }

    /// Overflowing subtraction. Returns `(wrapped_result, borrow_out)`.
    /// Same width choice as [`wrapping_sub`](Self::wrapping_sub);
    /// `borrow_out` is the underflow flag (`self < other`).
    pub fn overflowing_sub(&self, other: &Self) -> (Self, bool) {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let borrow = sub_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        (out, borrow)
    }

    /// Checked subtraction. `None` on underflow.
    pub fn checked_sub(&self, other: &Self) -> Option<Self> {
        let (res, borrow) = self.overflowing_sub(other);
        if borrow { None } else { Some(res) }
    }
}

// Mul lives in its own impl block because `CarryingMul` is not part of
// `MachineWord`'s supertrait chain — see `mul_slice`'s note.

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    HeaplessBigInt<T, CAP, P>
{
    /// Wrapping multiplication at the operands' width `max(a.len, b.len)`:
    /// keeps the low `width` words (`a·b mod 2^(width·word_bits)`),
    /// exactly like `FixedUInt<T, width>::wrapping_mul`. [`WideMul`] returns
    /// both halves.
    pub fn wrapping_mul(&self, other: &Self) -> Self {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        mul_slice(
            &self.limbs,
            self.len as usize,
            &other.limbs,
            other.len as usize,
            &mut out.limbs,
            out_len,
        );
        debug_assert!(zero_tail_ok(&out.limbs, out_len));
        out
    }

    /// Overflowing multiplication, at the operands' width
    /// `w = max(a.len, b.len)`. Returns `(a·b mod 2^(w·word_bits),
    /// overflow)`, where `overflow` is set iff the product does not fit
    /// in `w` words — bit-identical to `FixedUInt<T, w>::overflowing_mul`.
    /// The split is at the value width (via the widening [`CarryingMul`]), so
    /// the high half is the part beyond `w`; `CAP` is irrelevant.
    pub fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        let zero_v = <Self as const_num_traits::Zero>::zero();
        let (lo, hi) = <Self as CarryingMul>::carrying_mul(*self, *other, zero_v);
        (lo, !<Self as const_num_traits::Zero>::is_zero(&hi))
    }

    /// Checked multiplication. `None` when the product does not fit in the
    /// operands' width `max(a.len, b.len)` — exactly when
    /// `FixedUInt<T, width>::checked_mul` would return `None`.
    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        let (res, overflow) = self.overflowing_mul(other);
        if overflow { None } else { Some(res) }
    }
}

// ── const_num_traits CheckedAdd / CheckedMul (Nct only) ──
//
// The trait forms a downstream variable-time modular-inverse consumer binds
// on. `checked_add` / `checked_mul` return `None` on overflow at the
// operands' width, exactly as the same-width `FixedUInt` would. Trait
// exposure is kept Nct-only to match the existing surface.
// `HeaplessBigInt: Copy`, so bridging the by-value trait receiver to the
// by-reference inherent method is free.

impl<T, const CAP: usize> CheckedAdd for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn checked_add(self, v: Self) -> Option<Self> {
        Self::checked_add(&self, &v)
    }
}

impl<T, const CAP: usize> CheckedMul for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn checked_mul(self, v: Self) -> Option<Self> {
        Self::checked_mul(&self, &v)
    }
}

impl<T, const CAP: usize> CheckedSub for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn checked_sub(self, v: Self) -> Option<Self> {
        Self::checked_sub(&self, &v)
    }
}

// Reference-receiver mirrors: `(&h).checked_add(&g)` binds the same generic
// trait bound as the value form. The receiver and operand are already `&Self`,
// so these forward to the inherent by-ref methods (`checked_add(&self, &Self)`)
// rather than the by-value trait — no `[T; CAP]` copy of either operand.

impl<T, const CAP: usize> CheckedAdd for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn checked_add(self, v: Self) -> Option<Self::Output> {
        HeaplessBigInt::<T, CAP, Nct>::checked_add(self, v)
    }
}

impl<T, const CAP: usize> CheckedMul for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn checked_mul(self, v: Self) -> Option<Self::Output> {
        HeaplessBigInt::<T, CAP, Nct>::checked_mul(self, v)
    }
}

impl<T, const CAP: usize> CheckedSub for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn checked_sub(self, v: Self) -> Option<Self::Output> {
        HeaplessBigInt::<T, CAP, Nct>::checked_sub(self, v)
    }
}

// ── num_traits Checked{Add,Sub,Mul} (Nct only) ──
//
// The `num_traits::PrimInt` supertraits, bridging its by-reference receiver to
// the inherent by-reference method (same values as the const_num_traits forms
// above; different crate and receiver shape).

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::CheckedAdd for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    fn checked_add(&self, v: &Self) -> Option<Self> {
        Self::checked_add(self, v)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::CheckedSub for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    fn checked_sub(&self, v: &Self) -> Option<Self> {
        Self::checked_sub(self, v)
    }
}

#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::CheckedMul for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn checked_mul(&self, v: &Self) -> Option<Self> {
        Self::checked_mul(self, v)
    }
}

// ── const_num_traits Saturating{Add,Sub,Mul} (Nct only) ──
//
// Same gating as the Checked* trait forms above: the value-form trait
// delegates to the by-reference inherent method (free, `HeaplessBigInt: Copy`).
// The saturation target is the operand-width max/zero, not the CAP-wide
// `Bounded` — see `max_at_len`.

impl<T, const CAP: usize> SaturatingAdd for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn saturating_add(self, v: Self) -> Self {
        Self::saturating_add(&self, &v)
    }
}

impl<T, const CAP: usize> SaturatingSub for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = Self;
    fn saturating_sub(self, v: Self) -> Self {
        Self::saturating_sub(&self, &v)
    }
}

impl<T, const CAP: usize> SaturatingMul for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn saturating_mul(self, v: Self) -> Self {
        Self::saturating_mul(&self, &v)
    }
}

// ── Ct saturating: branchless select on the overflow/borrow flag ──
//
// The `Nct` forms above branch on the flag; the `Ct` forms pick the
// saturated sentinel vs the wrapped result with `ct_select` (the whole-value
// masked select), so timing doesn't reveal whether saturation happened. The
// sentinel is the operand-width max/zero, same as the Nct path. Additive —
// the `Nct` impls are untouched.

impl<T, const CAP: usize> SaturatingAdd for HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = Self;
    fn saturating_add(self, v: Self) -> Self {
        let (res, overflow) = OverflowingAdd::overflowing_add(self, v);
        ct_select(&res, &max_at_len(res.len), overflow)
    }
}

impl<T, const CAP: usize> SaturatingSub for HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = Self;
    fn saturating_sub(self, v: Self) -> Self {
        let (res, borrow) = OverflowingSub::overflowing_sub(self, v);
        ct_select(&res, &Self::new_zero_with_len(res.len), borrow)
    }
}

impl<T, const CAP: usize> SaturatingMul for HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + subtle::ConditionallySelectable,
{
    type Output = Self;
    fn saturating_mul(self, v: Self) -> Self {
        let (res, overflow) = OverflowingMul::overflowing_mul(self, v);
        ct_select(&res, &max_at_len(res.len), overflow)
    }
}

// Reference-receiver mirrors for both personalities: deref and forward to the
// matching value impl (`HeaplessBigInt: Copy`), so `(&h).saturating_add(&g)`
// resolves the same way `h.saturating_add(g)` does.

impl<T, const CAP: usize> SaturatingAdd for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn saturating_add(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as SaturatingAdd>::saturating_add(*self, *v)
    }
}

impl<T, const CAP: usize> SaturatingSub for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn saturating_sub(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as SaturatingSub>::saturating_sub(*self, *v)
    }
}

impl<T, const CAP: usize> SaturatingMul for &HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, Nct>;
    fn saturating_mul(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Nct> as SaturatingMul>::saturating_mul(*self, *v)
    }
}

impl<T, const CAP: usize> SaturatingAdd for &HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = HeaplessBigInt<T, CAP, Ct>;
    fn saturating_add(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as SaturatingAdd>::saturating_add(*self, *v)
    }
}

impl<T, const CAP: usize> SaturatingSub for &HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    type Output = HeaplessBigInt<T, CAP, Ct>;
    fn saturating_sub(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as SaturatingSub>::saturating_sub(*self, *v)
    }
}

impl<T, const CAP: usize> SaturatingMul for &HeaplessBigInt<T, CAP, Ct>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T> + subtle::ConditionallySelectable,
{
    type Output = HeaplessBigInt<T, CAP, Ct>;
    fn saturating_mul(self, v: Self) -> Self::Output {
        <HeaplessBigInt<T, CAP, Ct> as SaturatingMul>::saturating_mul(*self, *v)
    }
}

// ── Ct checked arithmetic: masked-return `CtOption` ──
//
// The overflow flag gates the `CtOption` mask instead of a branch, so a
// secret operand's overflow isn't leaked through an `Option` discriminant.
// No `ct_select` (or `ConditionallySelectable` bound) needed — the value is
// always the wrapped result; only its observability is masked. P-generic,
// like FixedUInt's.

impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtCheckedAdd
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn ct_checked_add(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, overflow) = self.overflowing_add(v);
        subtle::CtOption::new(val, subtle::Choice::from(!overflow as u8))
    }
}

impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtCheckedSub
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    fn ct_checked_sub(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, borrow) = self.overflowing_sub(v);
        subtle::CtOption::new(val, subtle::Choice::from(!borrow as u8))
    }
}

impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtCheckedMul
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    fn ct_checked_mul(&self, v: &Self) -> subtle::CtOption<Self> {
        let (val, overflow) = self.overflowing_mul(v);
        subtle::CtOption::new(val, subtle::Choice::from(!overflow as u8))
    }
}

// `num_traits::Saturating` (add/sub only) — deprecated upstream but still
// required by `num_traits::PrimInt`. Nct-only, matching the trait forms above.
#[cfg(feature = "num-traits")]
impl<T, const CAP: usize> num_traits::Saturating for HeaplessBigInt<T, CAP, Nct>
where
    T: MachineWord,
{
    fn saturating_add(self, v: Self) -> Self {
        <Self as SaturatingAdd>::saturating_add(self, v)
    }
    fn saturating_sub(self, v: Self) -> Self {
        <Self as SaturatingSub>::saturating_sub(self, v)
    }
}

// Trim trailing-zero limbs — NCT-implicit content scan sets `len` to
// `1 + index of highest non-zero limb` (or 0 for the mathematical zero).
// Called only from Nct code paths; exposed as a public method on the
// Nct-only impl block below.
fn trim_content<T: MachineWord, const CAP: usize, P: Personality>(
    mut v: HeaplessBigInt<T, CAP, P>,
) -> HeaplessBigInt<T, CAP, P> {
    // Scan the value's own words (0..len); the zero-tail invariant means
    // limbs beyond len are already zero, so CAP need not appear.
    let mut new_len: u16 = 0;
    let mut i = 0;
    while i < v.len as usize {
        if !is_zero(&v.limbs[i]) {
            new_len = (i + 1) as u16;
        }
        i += 1;
    }
    v.len = new_len;
    v
}

// Nct-only public trim: normalises `len` to match the actual value.
// Reasonable to call on any Nct-shape output whose `len` was inflated
// by upstream shape arithmetic (chained mul, add-with-CAP-headroom).

impl<T: MachineWord, const CAP: usize> HeaplessBigInt<T, CAP, Nct> {
    /// Trim `len` down to the highest non-zero limb + 1 (0 for zero).
    /// NCT-implicit — inspects limb content, so Nct-only.
    #[inline]
    pub fn trim(self) -> Self {
        trim_content(self)
    }

    /// Saturating addition: on overflow, the all-ones value at the operands'
    /// width `max(a.len, b.len)` (not the CAP-wide max), matching
    /// `FixedUInt<T, width>::saturating_add`. This inherent form branches on
    /// the overflow flag; the `Ct` carrier's branchless `SaturatingAdd` impl
    /// (via `ct_select`) is defined separately.
    pub fn saturating_add(&self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_add(other);
        if overflow { max_at_len(res.len) } else { res }
    }

    /// Saturating subtraction: clamps to zero at the operands' width on
    /// underflow. Nct-only, same reason as `saturating_add`.
    pub fn saturating_sub(&self, other: &Self) -> Self {
        let (res, borrow) = self.overflowing_sub(other);
        if borrow {
            Self::new_zero_with_len(res.len)
        } else {
            res
        }
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize>
    HeaplessBigInt<T, CAP, Nct>
{
    /// Saturating multiplication: on overflow, the all-ones value at the
    /// operands' width `max(a.len, b.len)`. Nct-only, same reason as
    /// `saturating_add`.
    pub fn saturating_mul(&self, other: &Self) -> Self {
        let (res, overflow) = self.overflowing_mul(other);
        if overflow { max_at_len(res.len) } else { res }
    }
}

// ── core::ops::{Add, Sub, Mul} — panic on overflow at the operand width ──
//
// Same contract as the same-width `FixedUInt`: forward to the
// `overflowing_*` op and panic (Nct) or wrap (Ct) if it flags. Callers
// wanting wrap or a flag use `wrapping_*` / `overflowing_*` / `checked_*`.

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Add<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn add(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, overflow) = self.overflowing_add(other);
        panic_on_overflow_if_nct::<P>(overflow, "HeaplessBigInt::add overflow");
        res
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Sub<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn sub(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, borrow) = self.overflowing_sub(other);
        panic_on_overflow_if_nct::<P>(borrow, "HeaplessBigInt::sub underflow");
        res
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::Mul<&HeaplessBigInt<T, CAP, P>> for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn mul(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, overflow) = self.overflowing_mul(other);
        panic_on_overflow_if_nct::<P>(overflow, "HeaplessBigInt::mul overflow");
        res
    }
}

// `HeaplessBigInt: Copy`, so forwarding these by-value operands to the
// `&Self` core is a no-op at runtime.
forward_arith_receivers!(Add, add);
forward_arith_receivers!(Sub, sub);
forward_arith_receivers!(Mul, mul + CarryingMul<Unsigned = T, Output = T>);

// ── Compound-assign forms (delegate to the operator, same panic/wrap rule) ──

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::AddAssign
    for HeaplessBigInt<T, CAP, P>
{
    fn add_assign(&mut self, other: Self) {
        self.add_assign(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality>
    core::ops::AddAssign<&HeaplessBigInt<T, CAP, P>> for HeaplessBigInt<T, CAP, P>
{
    fn add_assign(&mut self, other: &Self) {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let overflow = add_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        panic_on_overflow_if_nct::<P>(overflow, "HeaplessBigInt::add overflow");
        *self = out;
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::SubAssign
    for HeaplessBigInt<T, CAP, P>
{
    fn sub_assign(&mut self, other: Self) {
        self.sub_assign(&other);
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality>
    core::ops::SubAssign<&HeaplessBigInt<T, CAP, P>> for HeaplessBigInt<T, CAP, P>
{
    fn sub_assign(&mut self, other: &Self) {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let borrow = sub_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        panic_on_overflow_if_nct::<P>(borrow, "HeaplessBigInt::sub underflow");
        *self = out;
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::MulAssign for HeaplessBigInt<T, CAP, P>
{
    fn mul_assign(&mut self, other: Self) {
        self.mul_assign(&other);
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::MulAssign<&HeaplessBigInt<T, CAP, P>> for HeaplessBigInt<T, CAP, P>
{
    fn mul_assign(&mut self, other: &Self) {
        // Mirrors `overflowing_mul`: `carrying_mul` takes `Self` by value, so
        // this one copy is inherent to the primitive (same as the operator).
        let zero_v = <Self as const_num_traits::Zero>::zero();
        let (lo, hi) = <Self as CarryingMul>::carrying_mul(*self, *other, zero_v);
        let overflow = !<Self as const_num_traits::Zero>::is_zero(&hi);
        panic_on_overflow_if_nct::<P>(overflow, "HeaplessBigInt::mul overflow");
        *self = lo;
    }
}

// ── const_num_traits Wrapping / Overflowing Add & Sub ──
//
// Delegate to the inherent methods; the traits take `self` by value,
// the inherent methods take references. `HeaplessBigInt: Copy`, so
// converting between the two is a no-op at runtime.

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingAdd for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn wrapping_add(self, v: Self) -> Self::Output {
        Self::wrapping_add(&self, &v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingSub for HeaplessBigInt<T, CAP, P> {
    type Output = Self;
    fn wrapping_sub(self, v: Self) -> Self::Output {
        Self::wrapping_sub(&self, &v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingAdd
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn overflowing_add(self, v: Self) -> (Self::Output, bool) {
        Self::overflowing_add(&self, &v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingSub
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn overflowing_sub(self, v: Self) -> (Self::Output, bool) {
        Self::overflowing_sub(&self, &v)
    }
}

// Reference-receiver variants mirror `FixedUInt`'s pattern (`add_sub_impl.rs`),
// letting `&HeaplessBigInt` satisfy the same generic trait bound.

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingAdd for &HeaplessBigInt<T, CAP, P> {
    type Output = HeaplessBigInt<T, CAP, P>;
    fn wrapping_add(self, v: Self) -> Self::Output {
        HeaplessBigInt::wrapping_add(self, v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> WrappingSub for &HeaplessBigInt<T, CAP, P> {
    type Output = HeaplessBigInt<T, CAP, P>;
    fn wrapping_sub(self, v: Self) -> Self::Output {
        HeaplessBigInt::wrapping_sub(self, v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingAdd
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn overflowing_add(self, v: Self) -> (Self::Output, bool) {
        HeaplessBigInt::overflowing_add(self, v)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> OverflowingSub
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn overflowing_sub(self, v: Self) -> (Self::Output, bool) {
        HeaplessBigInt::overflowing_sub(self, v)
    }
}

// WrappingMul — explicit wrap-at-width multiply, for callers that want
// the low half rather than `core::ops::Mul`'s panic-on-overflow.

impl<T, const CAP: usize, P: Personality> WrappingMul for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn wrapping_mul(self, v: Self) -> Self::Output {
        Self::wrapping_mul(&self, &v)
    }
}

impl<T, const CAP: usize, P: Personality> WrappingMul for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn wrapping_mul(self, v: Self) -> Self::Output {
        HeaplessBigInt::wrapping_mul(self, v)
    }
}

// OverflowingMul — value-width overflow flag, matching FixedUInt.

impl<T, const CAP: usize, P: Personality> OverflowingMul for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = Self;
    fn overflowing_mul(self, v: Self) -> (Self::Output, bool) {
        Self::overflowing_mul(&self, &v)
    }
}

impl<T, const CAP: usize, P: Personality> OverflowingMul for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn overflowing_mul(self, v: Self) -> (Self::Output, bool) {
        HeaplessBigInt::overflowing_mul(self, v)
    }
}

// ── CarryingAdd at the bigint level ──
//
// `self + rhs + carry_in` with carry_out, over the operands' width
// (`max(self.len, rhs.len)`), not `CAP` — the symmetric partner of
// `borrowing_sub` below, same width rule as every other op. Same
// value-width result as `overflowing_add`; the difference is the
// `carry_in` input, which lets a multi-precision routine (wide-REDC)
// chain carries across limbs the way `borrowing_sub` chains borrows.

impl<T, const CAP: usize, P: Personality> CarryingAdd for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn carrying_add(self, rhs: Self, carry_in: bool) -> (Self::Output, bool) {
        let out_len = core::cmp::max(self.len as usize, rhs.len as usize);
        let mut out_limbs = [zero::<T>(); CAP];
        let mut carry = carry_in;
        let mut i = 0;
        while i < out_len {
            let (sum, c) = <T as CarryingAdd>::carrying_add(self.limbs[i], rhs.limbs[i], carry);
            out_limbs[i] = sum;
            carry = c;
            i += 1;
        }
        (
            HeaplessBigInt {
                limbs: out_limbs,
                len: out_len as u16,
                _p: PhantomData,
            },
            carry,
        )
    }
}

// Reference-receiver mirror (deref and forward, `HeaplessBigInt: Copy`).

impl<T, const CAP: usize, P: Personality> CarryingAdd for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn carrying_add(self, rhs: Self, carry_in: bool) -> (Self::Output, bool) {
        <HeaplessBigInt<T, CAP, P> as CarryingAdd>::carrying_add(*self, *rhs, carry_in)
    }
}

// `self - rhs - borrow_in` with borrow_out, over the operands' width
// (`max(self.len, rhs.len)`) — same width rule as `wrapping_sub`, so
// underflow wraps at the value's width. Used by multi-precision reduction.

impl<T, const CAP: usize, P: Personality> BorrowingSub for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn borrowing_sub(self, rhs: Self, borrow_in: bool) -> (Self::Output, bool) {
        let out_len = core::cmp::max(self.len as usize, rhs.len as usize);
        let mut out_limbs = [zero::<T>(); CAP];
        let mut borrow = borrow_in;
        let mut i = 0;
        while i < out_len {
            let (diff, br) =
                <T as BorrowingSub>::borrowing_sub(self.limbs[i], rhs.limbs[i], borrow);
            out_limbs[i] = diff;
            borrow = br;
            i += 1;
        }
        (
            HeaplessBigInt {
                limbs: out_limbs,
                len: out_len as u16,
                _p: PhantomData,
            },
            borrow,
        )
    }
}

// Reference-receiver mirror (deref and forward, `HeaplessBigInt: Copy`).

impl<T, const CAP: usize, P: Personality> BorrowingSub for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn borrowing_sub(self, rhs: Self, borrow_in: bool) -> (Self::Output, bool) {
        <HeaplessBigInt<T, CAP, P> as BorrowingSub>::borrowing_sub(*self, *rhs, borrow_in)
    }
}

// ── CarryingMul at the bigint level ──
//
// `(lo, hi) = self * rhs + carry (+ add)`, split at the operands' VALUE
// width `W = max(len)` words: `lo` = low W words, `hi` = high W words,
// reconstructing as `full = hi·2^(W·word_bits) + lo`. This matches
// `bits_precision()` (= `len·word_bits`) and the primitive contract
// (`200u8.wide_mul(200) = (64, 156)` splits at the type width) — and it
// is what a wide Montgomery reduction reads back, since it reconstructs
// against the operand's `bits_precision`, not the carrier's capacity.
//
// NOT `CAP`: for a sub-capacity field (`len < CAP` — e.g. a modulus
// narrower than the carrier) a CAP split would strand the high half in
// `lo` (`hi = 0`) and the REDC would be off by limbs. `CAP` is invisible
// here just like every other value-width op; the only fixed-width use of
// capacity is `ToBytes`'s owned holder. (For a full-width field
// `len == CAP`, so the two coincide.)

impl<T, const CAP: usize, P: Personality> CarryingMul for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Unsigned = Self;
    type Output = Self;

    fn carrying_mul(self, rhs: Self, carry: Self) -> (Self::Unsigned, Self::Output) {
        let zero_v = <Self as const_num_traits::Zero>::zero();
        self.carrying_mul_add(rhs, carry, zero_v)
    }

    fn carrying_mul_add(self, rhs: Self, carry: Self, add: Self) -> (Self::Unsigned, Self::Output) {
        // Split point W = the operands' value width. `carry`/`add` are
        // added into the low half, so W must also cover them.
        let w = core::cmp::max(
            core::cmp::max(self.len as usize, rhs.len as usize),
            core::cmp::max(carry.len as usize, add.len as usize),
        );
        let mut lo_limbs = [zero::<T>(); CAP];
        let mut hi_limbs = [zero::<T>(); CAP];

        // Schoolbook self * rhs into positions [0, 2W): pos < W → lo,
        // else hi[pos - W]. Iterate the operands' word counts (public
        // shape), not the array capacity.
        let a_n = self.len as usize;
        let b_n = rhs.len as usize;
        let mut i = 0;
        while i < a_n {
            let mut c = zero::<T>();
            let mut j = 0;
            while j < b_n {
                let pos = i + j;
                let (t_lo, t_hi) = <T as CarryingMul>::carrying_mul(self.limbs[i], rhs.limbs[j], c);
                let existing = if pos < w {
                    lo_limbs[pos]
                } else {
                    hi_limbs[pos - w]
                };
                let (sum, c1) = <T as CarryingAdd>::carrying_add(existing, t_lo, false);
                if pos < w {
                    lo_limbs[pos] = sum;
                } else {
                    hi_limbs[pos - w] = sum;
                }
                let (new_c, _) = <T as CarryingAdd>::carrying_add(t_hi, zero::<T>(), c1);
                c = new_c;
                j += 1;
            }
            // Row-final carry at column i + b_n.
            let tail = i + b_n;
            if tail < w {
                let (sum, _) = <T as CarryingAdd>::carrying_add(lo_limbs[tail], c, false);
                lo_limbs[tail] = sum;
            } else {
                let (sum, _) = <T as CarryingAdd>::carrying_add(hi_limbs[tail - w], c, false);
                hi_limbs[tail - w] = sum;
            }
            i += 1;
        }

        // Fold carry, then add, into the low half [0, W); overflow into hi.
        for src in [&carry, &add] {
            let mut cin = false;
            let mut i = 0;
            while i < w {
                let (sum, c) = <T as CarryingAdd>::carrying_add(lo_limbs[i], src.limbs[i], cin);
                lo_limbs[i] = sum;
                cin = c;
                i += 1;
            }
            // Propagate the fold carry into the hi half. `Nct` may stop the
            // moment the carry dies; `Ct` must sweep the full width so timing
            // is independent of where — or whether — the carry chain
            // terminates (a secret-dependent bound here leaks the operands,
            // which the taint gate catches). A `false` carry-in makes each
            // step a constant-time no-op.
            let mut i = 0;
            match P::TAG {
                PersonalityTag::Nct => {
                    while cin && i < w {
                        let (sum, c) =
                            <T as CarryingAdd>::carrying_add(hi_limbs[i], zero::<T>(), true);
                        hi_limbs[i] = sum;
                        cin = c;
                        i += 1;
                    }
                }
                PersonalityTag::Ct => {
                    while i < w {
                        let (sum, c) =
                            <T as CarryingAdd>::carrying_add(hi_limbs[i], zero::<T>(), cin);
                        hi_limbs[i] = sum;
                        cin = c;
                        i += 1;
                    }
                }
            }
        }

        let lo = HeaplessBigInt {
            limbs: lo_limbs,
            len: w as u16,
            _p: PhantomData,
        };
        let hi = HeaplessBigInt {
            limbs: hi_limbs,
            len: w as u16,
            _p: PhantomData,
        };
        (lo, hi)
    }
}

// Reference-receiver mirror: both widening-mul methods deref and forward to
// the value impl (`HeaplessBigInt: Copy`). Mirrors `FixedUInt`'s `&Self`
// `CarryingMul` in `extended_precision_impl.rs`.

impl<T, const CAP: usize, P: Personality> CarryingMul for &HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + CarryingMul<Unsigned = T, Output = T>,
{
    type Unsigned = HeaplessBigInt<T, CAP, P>;
    type Output = HeaplessBigInt<T, CAP, P>;

    fn carrying_mul(self, rhs: Self, carry: Self) -> (Self::Unsigned, Self::Output) {
        <HeaplessBigInt<T, CAP, P> as CarryingMul>::carrying_mul(*self, *rhs, *carry)
    }

    fn carrying_mul_add(self, rhs: Self, carry: Self, add: Self) -> (Self::Unsigned, Self::Output) {
        <HeaplessBigInt<T, CAP, P> as CarryingMul>::carrying_mul_add(*self, *rhs, *carry, *add)
    }
}

#[inline]
pub(crate) fn zero_tail_ok<T: MachineWord>(limbs: &[T], used: usize) -> bool {
    let mut i = used;
    while i < limbs.len() {
        if !is_zero(&limbs[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use const_num_traits::Zero;

    type H = HeaplessBigInt<u32, 8, Nct>; // 256-bit CAP

    #[test]
    fn saturation_is_operand_width_not_cap() {
        // Two len-1 (32-bit) values in a CAP-8 carrier: overflow saturates to
        // the 32-bit operand-width max, NOT the 256-bit CAP max — matching
        // FixedUInt<u32, 1>. This is what the fixed-width carrier harness can't
        // reach (its backings have width == CAP).
        let a = H::from_le_bytes(&0xFFFF_FFFFu32.to_le_bytes()); // len 1
        let one = H::from_le_bytes(&1u32.to_le_bytes());
        let s = SaturatingAdd::saturating_add(a, one);
        assert_eq!(s.len, 1);
        assert_eq!(s.limbs[0], 0xFFFF_FFFF);

        // 2^16 * 2^16 = 2^32 overflows the 32-bit width; saturates the same way.
        let big = H::from_le_bytes(&0x1_0000u32.to_le_bytes());
        let m = SaturatingMul::saturating_mul(big, big);
        assert_eq!(m.len, 1);
        assert_eq!(m.limbs[0], 0xFFFF_FFFF);
    }

    #[test]
    fn saturating_sub_clamps_to_zero_at_width() {
        let one = H::from_le_bytes(&1u32.to_le_bytes()); // len 1
        let two = H::from_le_bytes(&2u32.to_le_bytes());
        let s = SaturatingSub::saturating_sub(one, two);
        assert_eq!(s.len, 1);
        assert!(<H as Zero>::is_zero(&s));
    }

    #[test]
    fn checked_div_rem_by_zero_is_none() {
        let a = H::from_le_bytes(&100u32.to_le_bytes());
        let z = <H as Zero>::zero();
        assert_eq!(a.checked_div(&z), None);
        assert_eq!(a.checked_rem(&z), None);
        let seven = H::from_le_bytes(&7u32.to_le_bytes());
        assert_eq!(a.checked_div(&seven).unwrap().limbs[0], 14);
        assert_eq!(a.checked_rem(&seven).unwrap().limbs[0], 2);
    }

    // CtCheckedAdd/Sub/Mul: the value is always the wrapped result; is_some
    // masks overflow. Matches the plain checked_* value + overflow status.
    #[test]
    fn ct_checked_arithmetic() {
        use const_num_traits::ops::ct::{CtCheckedAdd, CtCheckedMul, CtCheckedSub};
        type Cc = HeaplessBigInt<u8, 4, Ct>;

        // No overflow: is_some, value matches.
        let a = Cc::from(100u32);
        let b = Cc::from(50u32);
        let s = a.ct_checked_add(&b);
        assert!(bool::from(s.is_some()));
        assert_eq!(s.unwrap(), Cc::from(150u32));
        assert!(bool::from(a.ct_checked_sub(&b).is_some()));
        assert!(bool::from(
            Cc::from(7u32).ct_checked_mul(&Cc::from(9u32)).is_some()
        ));

        // Overflow / underflow: is_none (masked).
        assert!(!bool::from(
            Cc::from(u32::MAX).ct_checked_add(&Cc::from(1u32)).is_some()
        ));
        assert!(!bool::from(
            Cc::from(0u32).ct_checked_sub(&Cc::from(1u32)).is_some()
        ));
        assert!(!bool::from(
            Cc::from(0x1_0000u32)
                .ct_checked_mul(&Cc::from(0x1_0000u32))
                .is_some()
        ));
    }

    // The branchless Ct saturating impls must produce the same values as the
    // Nct ones (including the saturate/clamp cases), at the operand width.
    #[test]
    fn ct_saturating_matches_nct() {
        type Cn = HeaplessBigInt<u8, 4, Nct>;
        type Cc = HeaplessBigInt<u8, 4, Ct>;
        let cases = [(100u32, 50u32), (u32::MAX, 1), (u32::MAX, u32::MAX), (5, 9)];
        for (a, b) in cases {
            assert_eq!(
                SaturatingAdd::saturating_add(Cc::from(a), Cc::from(b)),
                Cc::from(a.saturating_add(b)),
                "ct saturating_add({a},{b})"
            );
            assert_eq!(
                SaturatingSub::saturating_sub(Cc::from(a), Cc::from(b)),
                Cc::from(a.saturating_sub(b))
            );
            assert_eq!(
                SaturatingMul::saturating_mul(Cc::from(a), Cc::from(b)),
                Cc::from(a.saturating_mul(b))
            );
            // Cross-check the Nct forms agree with std too.
            assert_eq!(
                SaturatingAdd::saturating_add(Cn::from(a), Cn::from(b)),
                Cn::from(a.saturating_add(b))
            );
        }
    }

    // Reference-receiver trait forms resolve to the same value as the by-value
    // forms — one representative per family (Checked / Saturating / Carrying /
    // Borrowing), covering both the Nct and Ct saturating personalities.
    #[test]
    fn by_ref_matches_value() {
        let a = H::from(100u32);
        let b = H::from(7u32);
        assert_eq!(
            CheckedAdd::checked_add(&a, &b),
            CheckedAdd::checked_add(a, b)
        );
        assert_eq!(
            CheckedSub::checked_sub(&a, &b),
            CheckedSub::checked_sub(a, b)
        );
        assert_eq!(
            CheckedMul::checked_mul(&a, &b),
            CheckedMul::checked_mul(a, b)
        );
        assert_eq!(
            SaturatingAdd::saturating_add(&a, &b),
            SaturatingAdd::saturating_add(a, b)
        );
        assert_eq!(
            SaturatingSub::saturating_sub(&a, &b),
            SaturatingSub::saturating_sub(a, b)
        );
        assert_eq!(
            SaturatingMul::saturating_mul(&a, &b),
            SaturatingMul::saturating_mul(a, b)
        );
        assert_eq!(
            CarryingAdd::carrying_add(&a, &b, true),
            CarryingAdd::carrying_add(a, b, true)
        );
        assert_eq!(
            BorrowingSub::borrowing_sub(&a, &b, true),
            BorrowingSub::borrowing_sub(a, b, true)
        );
        let z = <H as Zero>::zero();
        assert_eq!(
            CarryingMul::carrying_mul(&a, &b, &z),
            CarryingMul::carrying_mul(a, b, z)
        );
        assert_eq!(
            CarryingMul::carrying_mul_add(&a, &b, &z, &b),
            CarryingMul::carrying_mul_add(a, b, z, b)
        );

        // Ct saturating &Self mirror resolves to the value form too.
        type Cc = HeaplessBigInt<u8, 4, Ct>;
        let ca = Cc::from(u32::MAX);
        let cb = Cc::from(1u32);
        assert_eq!(
            SaturatingAdd::saturating_add(&ca, &cb),
            SaturatingAdd::saturating_add(ca, cb)
        );
    }
}
