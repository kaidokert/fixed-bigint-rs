//! Add / Sub / Mul for `HeaplessBigInt`.
//!
//! Every op is written against public loop counts derived from operand
//! `len`s (per § Length arithmetic under operations in the spec) and
//! per-limb branchless primitives from `const_num_traits`. Iteration is
//! CT-safe under the "len is public" invariant regardless of
//! Personality, so the Nct and Ct arms share the same body for
//! Add/Sub/Mul. Personality dispatch only enters when the output
//! reporting shape differs (e.g. panic-on-overflow vs mask-select).

use super::{HeaplessBigInt, is_zero, zero};
use crate::MachineWord;
use const_num_traits::{
    BorrowingSub, CarryingAdd, CarryingMul, OverflowingAdd, OverflowingSub, Personality,
    WrappingAdd, WrappingMul, WrappingSub,
};
use core::marker::PhantomData;

// ── Free-function slice kernels ──
//
// Take `&[T]` / `&mut [T]` so a future refactor can share them with
// `fixed-bigint`'s existing algorithms (spec § Code sharing).

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
/// zero-initialised on entry. `out_n` is `min(a_n + b_n, CAP)`; a partial
/// product that would overflow past `out_n` is silently truncated (used
/// by wrapping-mul; overflow-detecting mul checks separately).
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
    /// Wrapping addition. Output `len = min(max(a.len, b.len) + 1, CAP)`
    /// per the spec. If the natural sum would need `CAP + 1` limbs, the
    /// top carry-out is silently discarded (wrapping semantics).
    pub fn wrapping_add(&self, other: &Self) -> Self {
        let max_len = core::cmp::max(self.len as usize, other.len as usize);
        let out_len = core::cmp::min(max_len + 1, CAP);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let _carry = add_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        debug_assert!(zero_tail_ok(&out.limbs, out_len));
        out
    }

    /// Overflowing addition. Returns the wrapped result and the carry-out
    /// beyond `out_len` limbs. Public overflow flag is a scalar; not
    /// content-derived shape.
    pub fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        let max_len = core::cmp::max(self.len as usize, other.len as usize);
        let out_len = core::cmp::min(max_len + 1, CAP);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let carry_full = add_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        let overflow = carry_full && out_len == CAP;
        (out, overflow)
    }

    /// Checked addition. `None` on overflow.
    pub fn checked_add(&self, other: &Self) -> Option<Self> {
        let (res, overflow) = self.overflowing_add(other);
        if overflow { None } else { Some(res) }
    }

    /// Wrapping subtraction. Output `len = max(a.len, b.len)`.
    /// If `self < other`, the value wraps modulo `2^(len * WORD_BITS)`.
    pub fn wrapping_sub(&self, other: &Self) -> Self {
        let out_len = core::cmp::max(self.len as usize, other.len as usize);
        let mut out = Self::new_zero_with_len(out_len as u16);
        let _borrow = sub_slice(&self.limbs, &other.limbs, &mut out.limbs, out_len);
        debug_assert!(zero_tail_ok(&out.limbs, out_len));
        out
    }

    /// Overflowing subtraction. Returns `(wrapped_result, borrow_out)`.
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
    /// Wrapping multiplication. Output `len = min(a.len + b.len, CAP)`.
    /// Products that would exceed `CAP` limbs are truncated.
    pub fn wrapping_mul(&self, other: &Self) -> Self {
        let out_len = core::cmp::min(self.len as usize + other.len as usize, CAP);
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

    /// Overflowing multiplication. Returns `(wrapped_result,
    /// overflow_flag)`. Overflow is set if the natural product would need
    /// more than `CAP` limbs.
    pub fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        let natural_len = self.len as usize + other.len as usize;
        let overflow = natural_len > CAP;
        let out_len = core::cmp::min(natural_len, CAP);
        let mut out = Self::new_zero_with_len(out_len as u16);
        mul_slice(
            &self.limbs,
            self.len as usize,
            &other.limbs,
            other.len as usize,
            &mut out.limbs,
            out_len,
        );
        (out, overflow)
    }

    /// Checked multiplication. `None` on overflow.
    pub fn checked_mul(&self, other: &Self) -> Option<Self> {
        let (res, overflow) = self.overflowing_mul(other);
        if overflow { None } else { Some(res) }
    }
}

// ── core::ops::{Add, Sub, Mul} — panic on overflow, forward to wrapping ──

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Add<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn add(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, overflow) = self.overflowing_add(other);
        assert!(!overflow, "HeaplessBigInt::add overflow");
        res
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> core::ops::Sub<&HeaplessBigInt<T, CAP, P>>
    for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn sub(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, borrow) = self.overflowing_sub(other);
        assert!(!borrow, "HeaplessBigInt::sub underflow");
        res
    }
}

impl<T: MachineWord + CarryingMul<Unsigned = T, Output = T>, const CAP: usize, P: Personality>
    core::ops::Mul<&HeaplessBigInt<T, CAP, P>> for &HeaplessBigInt<T, CAP, P>
{
    type Output = HeaplessBigInt<T, CAP, P>;
    fn mul(self, other: &HeaplessBigInt<T, CAP, P>) -> Self::Output {
        let (res, overflow) = self.overflowing_mul(other);
        assert!(!overflow, "HeaplessBigInt::mul overflow");
        res
    }
}

// Value + mixed-receiver variants — modmath's EEA `Signed<T>` arithmetic
// wants owned-owned `+`/`-`/`*`, owned-ref `*`, and ref-owned `-`. Each
// delegates to the `&Self op &Self` variant. `HeaplessBigInt: Copy` so
// forwarding by-value operands to references is a no-op at runtime.

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

// WrappingMul — the explicit method modmath's EEA should call instead
// of `core::ops::Mul`, which has no defined overflow contract.

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

// ── BorrowingSub at the bigint level ──
//
// Full-CAP `self - rhs - borrow_in` with borrow_out. Iteration is
// 0..CAP (not `self.len`) because widening-primitive semantics require
// the whole array range. Modmath's full CIOS driver fires from this.

impl<T, const CAP: usize, P: Personality> BorrowingSub for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord,
{
    type Output = Self;
    fn borrowing_sub(self, rhs: Self, borrow_in: bool) -> (Self::Output, bool) {
        let mut out_limbs = [zero::<T>(); CAP];
        let mut borrow = borrow_in;
        let mut i = 0;
        while i < CAP {
            let (diff, br) =
                <T as BorrowingSub>::borrowing_sub(self.limbs[i], rhs.limbs[i], borrow);
            out_limbs[i] = diff;
            borrow = br;
            i += 1;
        }
        (
            HeaplessBigInt {
                limbs: out_limbs,
                len: CAP as u16,
                _p: PhantomData,
            },
            borrow,
        )
    }
}

// ── CarryingMul at the bigint level ──
//
// `(lo, hi) = self * rhs + carry`, splitting the 2·CAP-limb natural
// product across two CAP-wide halves. Modmath's `WideMul` blanket
// impl fires from this, unlocking the Montgomery driver.
//
// Both output halves get `len = CAP` — a public shape derived from the
// type parameter, not from operand content. The full-CAP iteration
// discipline is deliberate: widening semantics require the whole array
// range, not the runtime-len subset.

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
        let mut lo_limbs = [zero::<T>(); CAP];
        let mut hi_limbs = [zero::<T>(); CAP];

        // Schoolbook self * rhs accumulating into positions [0, 2·CAP).
        let mut i = 0;
        while i < CAP {
            let mut c = zero::<T>();
            let mut j = 0;
            while j < CAP {
                let pos = i + j;
                let (t_lo, t_hi) = <T as CarryingMul>::carrying_mul(self.limbs[i], rhs.limbs[j], c);
                let existing = if pos < CAP {
                    lo_limbs[pos]
                } else {
                    hi_limbs[pos - CAP]
                };
                let (sum, c1) = <T as CarryingAdd>::carrying_add(existing, t_lo, false);
                if pos < CAP {
                    lo_limbs[pos] = sum;
                } else {
                    hi_limbs[pos - CAP] = sum;
                }
                let (new_c, _) = <T as CarryingAdd>::carrying_add(t_hi, zero::<T>(), c1);
                c = new_c;
                j += 1;
            }
            let (sum, _) = <T as CarryingAdd>::carrying_add(hi_limbs[i], c, false);
            hi_limbs[i] = sum;
            i += 1;
        }

        // Fold `carry` into the low half, propagating overflow into hi.
        let mut cin = false;
        let mut i = 0;
        while i < CAP {
            let (sum, c) = <T as CarryingAdd>::carrying_add(lo_limbs[i], carry.limbs[i], cin);
            lo_limbs[i] = sum;
            cin = c;
            i += 1;
        }
        let mut i = 0;
        while cin && i < CAP {
            let (sum, c) = <T as CarryingAdd>::carrying_add(hi_limbs[i], zero::<T>(), true);
            hi_limbs[i] = sum;
            cin = c;
            i += 1;
        }

        // Fold `add` into the low half the same way.
        let mut cin = false;
        let mut i = 0;
        while i < CAP {
            let (sum, c) = <T as CarryingAdd>::carrying_add(lo_limbs[i], add.limbs[i], cin);
            lo_limbs[i] = sum;
            cin = c;
            i += 1;
        }
        let mut i = 0;
        while cin && i < CAP {
            let (sum, c) = <T as CarryingAdd>::carrying_add(hi_limbs[i], zero::<T>(), true);
            hi_limbs[i] = sum;
            cin = c;
            i += 1;
        }

        let lo = HeaplessBigInt {
            limbs: lo_limbs,
            len: CAP as u16,
            _p: PhantomData,
        };
        let hi = HeaplessBigInt {
            limbs: hi_limbs,
            len: CAP as u16,
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
