//! `PartialEq` / `Eq` / `PartialOrd` / `Ord` for `HeaplessBigInt`, plus
//! `subtle::ConstantTimeEq` for the Ct comparison path.
//!
//! All value-based:
//! - `Eq`: walks `max(a.len, b.len)` limbs. Under the zero-tail invariant,
//!   `HeaplessBigInt<u32, N, _>` with `len = 0` compares equal to a
//!   `zero_full_cap()` (len = CAP) — both represent mathematical zero.
//! - `Ord`: walks MSB-to-LSB up to `max(a.len, b.len)`. Regular impl
//!   branches on limb content (NCT-implicit); Ct callers use
//!   `subtle::ConstantTimeGreater` / `ConstantTimeEq` separately.
//! - `subtle::ConstantTimeEq`: XOR-fold across `max(a.len, b.len)`.
//!   `black_box` guards against LLVM re-branchifying the fold.

use super::HeaplessBigInt;
use crate::MachineWord;
use const_num_traits::Personality;

// ── PartialEq / Eq (value-based) ──

impl<T: MachineWord, const CAP: usize, P: Personality> PartialEq for HeaplessBigInt<T, CAP, P> {
    fn eq(&self, other: &Self) -> bool {
        let n = core::cmp::max(self.len, other.len) as usize;
        let mut i = 0;
        while i < n {
            if self.limbs[i] != other.limbs[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Eq for HeaplessBigInt<T, CAP, P> {}

// ── PartialOrd / Ord (value-based, NCT-implicit) ──

impl<T: MachineWord, const CAP: usize, P: Personality> PartialOrd for HeaplessBigInt<T, CAP, P> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: MachineWord, const CAP: usize, P: Personality> Ord for HeaplessBigInt<T, CAP, P> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        let n = core::cmp::max(self.len, other.len) as usize;
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
}

// ── Hash (consistent with value-based Eq) ──

impl<T: MachineWord + core::hash::Hash, const CAP: usize, P: Personality> core::hash::Hash
    for HeaplessBigInt<T, CAP, P>
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        // Hash up to the highest non-zero limb, ignoring both `len` and
        // `CAP`, so `ConstZero::ZERO` and `zero_full_cap()` produce the
        // same hash (value-based). NCT-implicit — this scans content.
        let mut top = 0usize;
        let mut i = 0;
        while i < CAP {
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
