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

use super::{HeaplessBigInt, is_zero, zero};
use crate::MachineWord;
use const_num_traits::{
    BorrowingSub, CarryingAdd, CarryingMul, CheckedAdd, CheckedMul, Nct, OverflowingAdd,
    OverflowingMul, OverflowingSub, Personality, PersonalityTag, WrappingAdd, WrappingMul,
    WrappingSub,
};
use core::marker::PhantomData;

// The checked `+`/`-`/`*` operators panic on overflow at the operands'
// width. That panic branches on a data-dependent overflow bit, so it
// runs for `Nct` only; the `Ct` arm wraps silently (like `wrapping_*`),
// keeping control flow value-independent. Mirrors `FixedUInt`'s
// `maybe_panic_if::<P>`.
#[inline]
fn panic_on_overflow_if_nct<P: Personality>(overflow: bool, msg: &'static str) {
    match P::TAG {
        PersonalityTag::Nct => assert!(!overflow, "{}", msg),
        PersonalityTag::Ct => {}
    }
}

// ── Free-function slice kernels ──
//
// Take `&[T]` / `&mut [T]` so a future refactor can share them with
// `fixed-bigint`'s existing fixed-width algorithms.

/// `out[..n] = a[..n] + b[..n]`, returning the final carry-out.
/// All three slices must have length ≥ `n`. `a` / `b` beyond their
/// respective logical `len`s must be zero (zero-tail invariant).
#[inline]
pub(crate) fn add_slice<T: MachineWord>(a: &[T], b: &[T], out: &mut [T], n: usize) -> bool {
    let mut carry = false;
    let mut i = 0;
    while i < n {
        let (sum, c) = <T as CarryingAdd>::carrying_add(a[i], b[i], carry);
        out[i] = sum;
        carry = c;
        i += 1;
    }
    carry
}

/// `out[..n] = a[..n] - b[..n]`, returning the final borrow-out.
/// Same length / zero-tail preconditions as [`add_slice`].
#[inline]
pub(crate) fn sub_slice<T: MachineWord>(a: &[T], b: &[T], out: &mut [T], n: usize) -> bool {
    let mut borrow = false;
    let mut i = 0;
    while i < n {
        let (diff, br) = <T as BorrowingSub>::borrowing_sub(a[i], b[i], borrow);
        out[i] = diff;
        borrow = br;
        i += 1;
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

// Value + mixed-receiver variants for callers that want by-value operators:
// owned-owned `+`/`-`/`*`, owned-ref `*`, ref-owned `-`. Each delegates to
// the `&Self op &Self` variant. `HeaplessBigInt: Copy`, so forwarding
// by-value operands to references is a no-op at runtime.

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Add
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn add(self, other: Self) -> Self {
        (&self).add(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Add<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn add(self, other: &Self) -> Self {
        (&self).add(other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Add<HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn add(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.add(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Sub
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        (&self).sub(&other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Sub<&HeaplessBigInt<T, CAP, P>>
    for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn sub(self, other: &Self) -> Self {
        (&self).sub(other)
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Sub<HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn sub(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.sub(&other)
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::Mul for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        (&self).mul(&other)
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::Mul<&HeaplessBigInt<T, CAP, P>> for HeaplessBigInt<T, CAP, P>
{
    type Output = Self;
    fn mul(self, other: &Self) -> Self {
        (&self).mul(other)
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::Mul<HeaplessBigInt<T, CAP, P>> for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn mul(self, other: HeaplessBigInt<T, CAP, P>) -> Self::Output {
        self.mul(&other)
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
            let mut i = 0;
            while cin && i < w {
                let (sum, c) = <T as CarryingAdd>::carrying_add(hi_limbs[i], zero::<T>(), true);
                hi_limbs[i] = sum;
                cin = c;
                i += 1;
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
