//! `PartialEq` / `Eq` / `PartialOrd` / `Ord` for `HeaplessBigInt`, plus
//! `subtle::ConstantTimeEq` and `subtle::ConditionallySelectable` for
//! the Ct paths.
//!
//! All value-based, each dispatching on `P` like `FixedUInt`:
//! - `Eq`: walks `max(a.len, b.len)` limbs. `Nct` short-circuits at the
//!   first differing limb; `Ct` XOR/OR-folds every limb so timing does
//!   not reveal the first mismatch (the returned `bool` is still
//!   branchable — Ct-secure equality routes through `ConstantTimeEq`).
//!   Under the zero-tail invariant, `HeaplessBigInt<u32, N, _>` with
//!   `len = 0` compares equal to a `zero_full_cap()` (len = CAP).
//! - `Ord`: MSB-to-LSB up to `max(a.len, b.len)`. `Nct` short-circuits;
//!   `Ct` scans the full width with an `undecided` lock (no early return).
//! - `subtle::ConstantTimeEq`: XOR-fold across `max(a.len, b.len)`.
//!   `black_box` guards against LLVM re-branchifying the fold.
//! - `subtle::ConditionallySelectable`: per-limb branchless select via
//!   `T`'s subtle impl, iterating up to `max(a.len, b.len)`. Output len
//!   is that same `max`, a public shape derived from two public shape
//!   parameters — never from `choice`.
//! - `const_num_traits::CtIsZero`: AND-fold `T::ct_eq(&ZERO)` across
//!   `0..self.len`. Limbs beyond `len` are zero by invariant so
//!   skipping them preserves the answer.
//! - `subtle::ConstantTimeGreater` / `ConstantTimeLess`: MSB-to-LSB
//!   scan up to `max(a.len, b.len)` with a running `undecided` bit —
//!   the Montgomery conditional-subtract shape.

use super::{HeaplessBigInt, is_zero, zero};
use crate::MachineWord;
use const_num_traits::{Personality, PersonalityTag};
use core::marker::PhantomData;

// ── PartialEq / Eq (value-based) ──

impl<T: MachineWord, const CAP: usize, P: Personality> PartialEq for HeaplessBigInt<T, CAP, P> {
    fn eq(&self, other: &Self) -> bool {
        let n = core::cmp::max(self.len, other.len) as usize;
        match P::TAG {
            PersonalityTag::Nct => {
                let mut i = 0;
                while i < n {
                    if self.limbs[i] != other.limbs[i] {
                        return false;
                    }
                    i += 1;
                }
                true
            }
            // Fold every limb, no early return: timing is independent of
            // where the first mismatch is.
            PersonalityTag::Ct => {
                let mut diff = zero::<T>();
                let mut i = 0;
                while i < n {
                    diff |= self.limbs[i] ^ other.limbs[i];
                    i += 1;
                }
                is_zero(&diff)
            }
        }
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Eq for HeaplessBigInt<T, CAP, P> {}

// ── PartialOrd / Ord (value-based) ──

impl<T: MachineWord, const CAP: usize, P: Personality> PartialOrd for HeaplessBigInt<T, CAP, P> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Ord for HeaplessBigInt<T, CAP, P> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let n = core::cmp::max(self.len, other.len) as usize;
        match P::TAG {
            PersonalityTag::Nct => {
                let mut i = n;
                while i > 0 {
                    i -= 1;
                    match self.limbs[i].cmp(&other.limbs[i]) {
                        core::cmp::Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                core::cmp::Ordering::Equal
            }
            // Full MSB-to-LSB scan; once a differing limb is seen the
            // `decided` mask stops later limbs from overturning it. Mirrors
            // `FixedUInt`'s `const_cmp_ct`. result: 2 = Greater, 1 = Less.
            // Shared full-width branchless scan (see `const_cmp_ct`); the two
            // operand slices are equal length (`n`).
            PersonalityTag::Ct => {
                crate::fixeduint::const_cmp_ct(&self.limbs[..n], &other.limbs[..n])
            }
        }
    }
}

// ── Hash (consistent with value-based Eq) ──

impl<T: MachineWord + core::hash::Hash, const CAP: usize, P: Personality> core::hash::Hash
    for HeaplessBigInt<T, CAP, P>
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        // Hash up to the highest non-zero limb, ignoring `len` so equal
        // values at different shapes hash alike (value-based). Scans
        // `0..len`; limbs beyond `len` are zero by invariant, so `CAP`
        // need not enter. NCT-implicit — this scans content.
        let mut top = 0usize;
        let mut i = 0;
        while i < self.len as usize {
            if !super::is_zero(&self.limbs[i]) {
                top = i + 1;
            }
            i += 1;
        }
        state.write_usize(top);
        for limb in &self.limbs[..top] {
            limb.hash(state);
        }
    }
}

// ── subtle::ConstantTimeEq (Ct-safe equality) ──

impl<T, const CAP: usize, P: Personality> subtle::ConstantTimeEq for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_eq(&self, other: &Self) -> subtle::Choice {
        // Iterate `max(len)` — a public shape parameter. Both operands
        // walk the same public count regardless of value.
        let n = core::cmp::max(self.len, other.len) as usize;
        let mut acc = subtle::Choice::from(1u8);
        let mut i = 0;
        while i < n {
            let per_limb = self.limbs[i].ct_eq(&other.limbs[i]);
            acc &= per_limb;
            i += 1;
        }
        // `black_box` on the accumulator so LLVM can't recognise the
        // AND-fold as a short-circuit — same defence as
        // FixedUInt's `const_ct_select`.
        subtle::Choice::from(core::hint::black_box(acc.unwrap_u8()))
    }
}

// ── subtle::ConditionallySelectable ──

impl<T, const CAP: usize, P: Personality> subtle::ConditionallySelectable
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConditionallySelectable,
{
    fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
        // Output `len = max(a.len, b.len)`. Both operand lens are public
        // shape parameters, so their `max` is public — never derived
        // from `choice`. Per-limb select up to that bound; the tails
        // beyond each operand's own len are zero (zero-tail invariant),
        // so per-limb select on the tails yields zero regardless of
        // `choice`, and the output's tail past `out_len` stays zero.
        let out_len = core::cmp::max(a.len, b.len);
        let mut limbs = [super::zero::<T>(); CAP];
        let mut i = 0;
        while i < out_len as usize {
            limbs[i] = <T as subtle::ConditionallySelectable>::conditional_select(
                &a.limbs[i],
                &b.limbs[i],
                choice,
            );
            i += 1;
        }
        Self {
            limbs,
            len: out_len,
            _p: PhantomData,
        }
    }
}

// ── const_num_traits::CtIsZero ──

impl<T, const CAP: usize, P: Personality> const_num_traits::ops::ct::CtIsZero
    for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq,
{
    fn ct_is_zero(&self) -> subtle::Choice {
        let n = self.len as usize;
        let mut acc = subtle::Choice::from(1u8);
        let mut i = 0;
        while i < n {
            acc &= self.limbs[i].ct_eq(&<T as const_num_traits::ConstZero>::ZERO);
            i += 1;
        }
        subtle::Choice::from(core::hint::black_box(acc.unwrap_u8()))
    }
}

// ── subtle::ConstantTimeGreater / ConstantTimeLess ──

impl<T, const CAP: usize, P: Personality> subtle::ConstantTimeGreater for HeaplessBigInt<T, CAP, P>
where
    T: MachineWord + subtle::ConstantTimeEq + subtle::ConstantTimeGreater,
{
    fn ct_gt(&self, other: &Self) -> subtle::Choice {
        // MSB-to-LSB scan across `max(a.len, b.len)`. `undecided` locks
        // the answer at the first differing limb without a data-dependent
        // branch — every iteration always executes.
        let n = core::cmp::max(self.len, other.len) as usize;
        let mut gt = subtle::Choice::from(0u8);
        let mut undecided = subtle::Choice::from(1u8);
        let mut i = n;
        while i > 0 {
            i -= 1;
            let gt_here = self.limbs[i].ct_gt(&other.limbs[i]);
            let eq_here = self.limbs[i].ct_eq(&other.limbs[i]);
            gt |= undecided & gt_here;
            undecided &= eq_here;
        }
        gt
    }
}

// `ConstantTimeLess` is derived from `ConstantTimeEq` + `ConstantTimeGreater`
// via its default methods; the empty impl is enough to opt in.
impl<T, const CAP: usize, P: Personality> subtle::ConstantTimeLess for HeaplessBigInt<T, CAP, P> where
    T: MachineWord + subtle::ConstantTimeEq + subtle::ConstantTimeGreater
{
}
