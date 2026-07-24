//! HeaplessBigInt constant-time fixtures — the runtime-`len` carrier held at
//! full CAP width so it behaves bit-for-bit like `FixedUInt<T, CAP>`.
//!
//! Mirrors the `FixedUInt` fixtures (`fixtures_cat_{a,b,c}` / `_ct_traits`)
//! for `HeaplessBigInt<T, CAP, Ct>`. Construction is `from_limbs(a, CAP)` so
//! `len == CAP` (no zero-tail, full-width value); extraction is `all_limbs()`.
//! Same five `(T, CAP)` diagonals as the FixedUInt set:
//!   (u8, 16), (u16, 16), (u32, 4), (u32, 16), (u64, 4)
//!
//! Symbols are prefixed `ct_fix__H<cat>__*` (H for heapless) so the driver
//! scans them alongside the FixedUInt fixtures. Categories mirror the
//! FixedUInt split:
//!   - `HA`  — Ct arms dispatched via `match P::TAG`
//!   - `HB`  — `subtle::*` trait impls (ct_eq/gt/lt, conditional_select)
//!   - `HC`  — always-CT-by-construction ops (bitwise, wrapping/carry chains)
//!   - `HCT` — const-num-traits `Ct*` masked-return trait impls
//!
//! Behind the `heapless` cargo feature, which the asm-grep driver enables.
//! The runtime-`len` carrier's per-limb helpers loop over a public-but-runtime
//! width; each is attested public-bounded in ct-driver's `HELPER_ALLOWLIST`,
//! so these fixtures are gated on every target like the FixedUInt set.
//!
//! Shifts included: the `Ct` `<<`/`>>` operators dispatch to branchless
//! barrels (`const_shl_ct`/`const_shr_ct`), and `is_one` folds through the
//! out-of-line `const_is_one_ct` helper so its `len` loop lands in an
//! attestable symbol rather than inlining into the fixture.

use core::ops::{BitAnd, BitOr, BitXor, Not};

use const_num_traits::ops::ct::{
    CtCheckedAdd, CtCheckedMul, CtCheckedSub, CtIsPowerOfTwo, CtIsZero, CtParity,
};
use const_num_traits::Ct;
use const_num_traits::CtNonZero;
use const_num_traits::{
    AbsDiff, CarryingAdd, IsPowerOfTwo, Midpoint, NextPowerOfTwo, One, OverflowingAdd, PrimBits,
    SaturatingAdd, SaturatingMul, SaturatingSub, UnboundedShl, UnboundedShr, WrappingMul, Zero,
};
use fixed_bigint::HeaplessBigInt;
use subtle::{ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

use crate::{
    ct_fix_bin, ct_fix_checked_bin, ct_fix_checked_un, ct_fix_count, ct_fix_pred, ct_fix_pred2,
    ct_fix_shift, ct_fix_un,
};

// =============================================================================
// Ct shifts. The `<<`/`>>` operators dispatch on P::TAG, so a secret amount
// routes through the branchless barrels (const_shl_ct / const_shr_ct). Also
// covers is_power_of_two (no shift), next_power_of_two (via ct_shl), and
// midpoint (>> 1).
// =============================================================================

macro_rules! emit_h_shl_usize {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *(x << n).all_limbs()
        });
    };
}
emit_h_shl_usize!(ct_fix__HA__shl_usize__u8__N16, u8, 16);
emit_h_shl_usize!(ct_fix__HA__shl_usize__u16__N16, u16, 16);
emit_h_shl_usize!(ct_fix__HA__shl_usize__u32__N4, u32, 4);
emit_h_shl_usize!(ct_fix__HA__shl_usize__u32__N16, u32, 16);
emit_h_shl_usize!(ct_fix__HA__shl_usize__u64__N4, u64, 4);

macro_rules! emit_h_shr_usize {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *(x >> n).all_limbs()
        });
    };
}
emit_h_shr_usize!(ct_fix__HA__shr_usize__u8__N16, u8, 16);
emit_h_shr_usize!(ct_fix__HA__shr_usize__u16__N16, u16, 16);
emit_h_shr_usize!(ct_fix__HA__shr_usize__u32__N4, u32, 4);
emit_h_shr_usize!(ct_fix__HA__shr_usize__u32__N16, u32, 16);
emit_h_shr_usize!(ct_fix__HA__shr_usize__u64__N4, u64, 4);

// `<<=` / `>>=` — distinct assign impls with their own P::TAG dispatch,
// routing the Ct arm through the same barrels as `<<`/`>>`.
macro_rules! emit_h_shl_assign {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let mut x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            x <<= n;
            *x.all_limbs()
        });
    };
}
emit_h_shl_assign!(ct_fix__HA__shl_assign__u8__N16, u8, 16);
emit_h_shl_assign!(ct_fix__HA__shl_assign__u16__N16, u16, 16);
emit_h_shl_assign!(ct_fix__HA__shl_assign__u32__N4, u32, 4);
emit_h_shl_assign!(ct_fix__HA__shl_assign__u32__N16, u32, 16);
emit_h_shl_assign!(ct_fix__HA__shl_assign__u64__N4, u64, 4);

macro_rules! emit_h_shr_assign {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let mut x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            x >>= n;
            *x.all_limbs()
        });
    };
}
emit_h_shr_assign!(ct_fix__HA__shr_assign__u8__N16, u8, 16);
emit_h_shr_assign!(ct_fix__HA__shr_assign__u16__N16, u16, 16);
emit_h_shr_assign!(ct_fix__HA__shr_assign__u32__N4, u32, 4);
emit_h_shr_assign!(ct_fix__HA__shr_assign__u32__N16, u32, 16);
emit_h_shr_assign!(ct_fix__HA__shr_assign__u64__N4, u64, 4);

// `Shl<u32>` / `Shr<u32>` — the u32 operator forms delegate to the usize
// impls; fixtured here since the FixedUInt side only covers `<< u32` (asym).
macro_rules! emit_h_shl_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *(x << n).all_limbs()
        });
    };
}
emit_h_shl_u32!(ct_fix__HA__shl_u32__u8__N16, u8, 16);
emit_h_shl_u32!(ct_fix__HA__shl_u32__u16__N16, u16, 16);
emit_h_shl_u32!(ct_fix__HA__shl_u32__u32__N4, u32, 4);
emit_h_shl_u32!(ct_fix__HA__shl_u32__u32__N16, u32, 16);
emit_h_shl_u32!(ct_fix__HA__shl_u32__u64__N4, u64, 4);

macro_rules! emit_h_shr_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *(x >> n).all_limbs()
        });
    };
}
emit_h_shr_u32!(ct_fix__HA__shr_u32__u8__N16, u8, 16);
emit_h_shr_u32!(ct_fix__HA__shr_u32__u16__N16, u16, 16);
emit_h_shr_u32!(ct_fix__HA__shr_u32__u32__N4, u32, 4);
emit_h_shr_u32!(ct_fix__HA__shr_u32__u32__N16, u32, 16);
emit_h_shr_u32!(ct_fix__HA__shr_u32__u64__N4, u64, 4);

macro_rules! emit_h_unbounded_shl {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *UnboundedShl::unbounded_shl(x, n).all_limbs()
        });
    };
}
emit_h_unbounded_shl!(ct_fix__HA__unbounded_shl__u8__N16, u8, 16);
emit_h_unbounded_shl!(ct_fix__HA__unbounded_shl__u16__N16, u16, 16);
emit_h_unbounded_shl!(ct_fix__HA__unbounded_shl__u32__N4, u32, 4);
emit_h_unbounded_shl!(ct_fix__HA__unbounded_shl__u32__N16, u32, 16);
emit_h_unbounded_shl!(ct_fix__HA__unbounded_shl__u64__N4, u64, 4);

macro_rules! emit_h_unbounded_shr {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *UnboundedShr::unbounded_shr(x, n).all_limbs()
        });
    };
}
emit_h_unbounded_shr!(ct_fix__HA__unbounded_shr__u8__N16, u8, 16);
emit_h_unbounded_shr!(ct_fix__HA__unbounded_shr__u16__N16, u16, 16);
emit_h_unbounded_shr!(ct_fix__HA__unbounded_shr__u32__N4, u32, 4);
emit_h_unbounded_shr!(ct_fix__HA__unbounded_shr__u32__N16, u32, 16);
emit_h_unbounded_shr!(ct_fix__HA__unbounded_shr__u64__N4, u64, 4);

// is_power_of_two (predicate, no shift), next_power_of_two (via ct_shl barrel).
macro_rules! emit_h_is_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            IsPowerOfTwo::is_power_of_two(x) as u8
        });
    };
}
emit_h_is_pow2!(ct_fix__HA__is_pow2__u8__N16, u8, 16);
emit_h_is_pow2!(ct_fix__HA__is_pow2__u16__N16, u16, 16);
emit_h_is_pow2!(ct_fix__HA__is_pow2__u32__N4, u32, 4);
emit_h_is_pow2!(ct_fix__HA__is_pow2__u32__N16, u32, 16);
emit_h_is_pow2!(ct_fix__HA__is_pow2__u64__N4, u64, 4);

macro_rules! emit_h_next_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            *NextPowerOfTwo::next_power_of_two(x).all_limbs()
        });
    };
}
emit_h_next_pow2!(ct_fix__HA__next_pow2__u8__N16, u8, 16);
emit_h_next_pow2!(ct_fix__HA__next_pow2__u16__N16, u16, 16);
emit_h_next_pow2!(ct_fix__HA__next_pow2__u32__N4, u32, 4);
emit_h_next_pow2!(ct_fix__HA__next_pow2__u32__N16, u32, 16);
emit_h_next_pow2!(ct_fix__HA__next_pow2__u64__N4, u64, 4);

macro_rules! emit_h_midpoint {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            *Midpoint::midpoint(x, y).all_limbs()
        });
    };
}
emit_h_midpoint!(ct_fix__HC__midpoint__u8__N16, u8, 16);
emit_h_midpoint!(ct_fix__HC__midpoint__u16__N16, u16, 16);
emit_h_midpoint!(ct_fix__HC__midpoint__u32__N4, u32, 4);
emit_h_midpoint!(ct_fix__HC__midpoint__u32__N16, u32, 16);
emit_h_midpoint!(ct_fix__HC__midpoint__u64__N4, u64, 4);

// =============================================================================
// Category HA: Ct arms dispatched via `match P::TAG`.
// =============================================================================

// SaturatingAdd / Sub / Mul
macro_rules! emit_h_sat_add {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = SaturatingAdd::saturating_add(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_sat_add!(ct_fix__HA__sat_add__u8__N16, u8, 16);
emit_h_sat_add!(ct_fix__HA__sat_add__u16__N16, u16, 16);
emit_h_sat_add!(ct_fix__HA__sat_add__u32__N4, u32, 4);
emit_h_sat_add!(ct_fix__HA__sat_add__u32__N16, u32, 16);
emit_h_sat_add!(ct_fix__HA__sat_add__u64__N4, u64, 4);

macro_rules! emit_h_sat_sub {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = SaturatingSub::saturating_sub(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_sat_sub!(ct_fix__HA__sat_sub__u8__N16, u8, 16);
emit_h_sat_sub!(ct_fix__HA__sat_sub__u16__N16, u16, 16);
emit_h_sat_sub!(ct_fix__HA__sat_sub__u32__N4, u32, 4);
emit_h_sat_sub!(ct_fix__HA__sat_sub__u32__N16, u32, 16);
emit_h_sat_sub!(ct_fix__HA__sat_sub__u64__N4, u64, 4);

macro_rules! emit_h_sat_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = SaturatingMul::saturating_mul(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_sat_mul!(ct_fix__HA__sat_mul__u8__N16, u8, 16);
emit_h_sat_mul!(ct_fix__HA__sat_mul__u16__N16, u16, 16);
emit_h_sat_mul!(ct_fix__HA__sat_mul__u32__N4, u32, 4);
emit_h_sat_mul!(ct_fix__HA__sat_mul__u32__N16, u32, 16);
emit_h_sat_mul!(ct_fix__HA__sat_mul__u64__N4, u64, 4);

// AbsDiff
macro_rules! emit_h_abs_diff {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = AbsDiff::abs_diff(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_abs_diff!(ct_fix__HA__abs_diff__u8__N16, u8, 16);
emit_h_abs_diff!(ct_fix__HA__abs_diff__u16__N16, u16, 16);
emit_h_abs_diff!(ct_fix__HA__abs_diff__u32__N4, u32, 4);
emit_h_abs_diff!(ct_fix__HA__abs_diff__u32__N16, u32, 16);
emit_h_abs_diff!(ct_fix__HA__abs_diff__u64__N4, u64, 4);

// PrimBits::leading_zeros / trailing_zeros
macro_rules! emit_h_lz {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            PrimBits::leading_zeros(x)
        });
    };
}
emit_h_lz!(ct_fix__HA__leading_zeros__u8__N16, u8, 16);
emit_h_lz!(ct_fix__HA__leading_zeros__u16__N16, u16, 16);
emit_h_lz!(ct_fix__HA__leading_zeros__u32__N4, u32, 4);
emit_h_lz!(ct_fix__HA__leading_zeros__u32__N16, u32, 16);
emit_h_lz!(ct_fix__HA__leading_zeros__u64__N4, u64, 4);

macro_rules! emit_h_tz {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            PrimBits::trailing_zeros(x)
        });
    };
}
emit_h_tz!(ct_fix__HA__trailing_zeros__u8__N16, u8, 16);
emit_h_tz!(ct_fix__HA__trailing_zeros__u16__N16, u16, 16);
emit_h_tz!(ct_fix__HA__trailing_zeros__u32__N4, u32, 4);
emit_h_tz!(ct_fix__HA__trailing_zeros__u32__N16, u32, 16);
emit_h_tz!(ct_fix__HA__trailing_zeros__u64__N4, u64, 4);

// Zero::is_zero / One::is_one
macro_rules! emit_h_is_zero {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            <HeaplessBigInt<$T, $N, Ct> as Zero>::is_zero(&x) as u8
        });
    };
}
emit_h_is_zero!(ct_fix__HA__is_zero__u8__N16, u8, 16);
emit_h_is_zero!(ct_fix__HA__is_zero__u16__N16, u16, 16);
emit_h_is_zero!(ct_fix__HA__is_zero__u32__N4, u32, 4);
emit_h_is_zero!(ct_fix__HA__is_zero__u32__N16, u32, 16);
emit_h_is_zero!(ct_fix__HA__is_zero__u64__N4, u64, 4);

macro_rules! emit_h_is_one {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            <HeaplessBigInt<$T, $N, Ct> as One>::is_one(&x) as u8
        });
    };
}
emit_h_is_one!(ct_fix__HA__is_one__u8__N16, u8, 16);
emit_h_is_one!(ct_fix__HA__is_one__u16__N16, u16, 16);
emit_h_is_one!(ct_fix__HA__is_one__u32__N4, u32, 4);
emit_h_is_one!(ct_fix__HA__is_one__u32__N16, u32, 16);
emit_h_is_one!(ct_fix__HA__is_one__u64__N4, u64, 4);

// PartialEq::eq — the `==` operator's branchless Ct XOR-fold, distinct from
// the `subtle::ct_eq` fixtured in category HB.
macro_rules! emit_h_eq {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            (x == y) as u8
        });
    };
}
emit_h_eq!(ct_fix__HA__eq__u8__N16, u8, 16);
emit_h_eq!(ct_fix__HA__eq__u16__N16, u16, 16);
emit_h_eq!(ct_fix__HA__eq__u32__N4, u32, 4);
emit_h_eq!(ct_fix__HA__eq__u32__N16, u32, 16);
emit_h_eq!(ct_fix__HA__eq__u64__N4, u64, 4);

// =============================================================================
// Category HB: subtle::* trait impls.
// =============================================================================

macro_rules! emit_h_ct_eq {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            x.ct_eq(&y).unwrap_u8()
        });
    };
}
emit_h_ct_eq!(ct_fix__HB__ct_eq__u8__N16, u8, 16);
emit_h_ct_eq!(ct_fix__HB__ct_eq__u16__N16, u16, 16);
emit_h_ct_eq!(ct_fix__HB__ct_eq__u32__N4, u32, 4);
emit_h_ct_eq!(ct_fix__HB__ct_eq__u32__N16, u32, 16);
emit_h_ct_eq!(ct_fix__HB__ct_eq__u64__N4, u64, 4);

macro_rules! emit_h_ct_gt {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            x.ct_gt(&y).unwrap_u8()
        });
    };
}
emit_h_ct_gt!(ct_fix__HB__ct_gt__u8__N16, u8, 16);
emit_h_ct_gt!(ct_fix__HB__ct_gt__u16__N16, u16, 16);
emit_h_ct_gt!(ct_fix__HB__ct_gt__u32__N4, u32, 4);
emit_h_ct_gt!(ct_fix__HB__ct_gt__u32__N16, u32, 16);
emit_h_ct_gt!(ct_fix__HB__ct_gt__u64__N4, u64, 4);

macro_rules! emit_h_ct_lt {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            x.ct_lt(&y).unwrap_u8()
        });
    };
}
emit_h_ct_lt!(ct_fix__HB__ct_lt__u8__N16, u8, 16);
emit_h_ct_lt!(ct_fix__HB__ct_lt__u16__N16, u16, 16);
emit_h_ct_lt!(ct_fix__HB__ct_lt__u32__N4, u32, 4);
emit_h_ct_lt!(ct_fix__HB__ct_lt__u32__N16, u32, 16);
emit_h_ct_lt!(ct_fix__HB__ct_lt__u64__N4, u64, 4);

// ConditionallySelectable::conditional_select — takes a Choice built from an
// extra u8 arg (0 or 1). Mirrors the FixedUInt `cond_select` fixture.
macro_rules! emit_h_cond_select {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            choice: u8,
            out_ptr: *mut [$T; $N],
        ) {
            let a_arr = core::hint::black_box(unsafe { *a_ptr });
            let b_arr = core::hint::black_box(unsafe { *b_ptr });
            let c = core::hint::black_box(choice);
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a_arr, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b_arr, $N as u16);
            let r = <HeaplessBigInt<$T, $N, Ct> as subtle::ConditionallySelectable>::conditional_select(
                &x,
                &y,
                subtle::Choice::from(c),
            );
            let result = core::hint::black_box(*r.all_limbs());
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_cond_select!($name, $T, $N););
    };
}
emit_h_cond_select!(ct_fix__HB__cond_select__u8__N16, u8, 16);
emit_h_cond_select!(ct_fix__HB__cond_select__u16__N16, u16, 16);
emit_h_cond_select!(ct_fix__HB__cond_select__u32__N4, u32, 4);
emit_h_cond_select!(ct_fix__HB__cond_select__u32__N16, u32, 16);
emit_h_cond_select!(ct_fix__HB__cond_select__u64__N4, u64, 4);

// =============================================================================
// Category HC: always-CT-by-construction ops (regression watch).
// =============================================================================

// Bitwise: Not / BitAnd / BitOr / BitXor
macro_rules! emit_h_not {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let r = Not::not(x);
            *r.all_limbs()
        });
    };
}
emit_h_not!(ct_fix__HC__not__u8__N16, u8, 16);
emit_h_not!(ct_fix__HC__not__u16__N16, u16, 16);
emit_h_not!(ct_fix__HC__not__u32__N4, u32, 4);
emit_h_not!(ct_fix__HC__not__u32__N16, u32, 16);
emit_h_not!(ct_fix__HC__not__u64__N4, u64, 4);

macro_rules! emit_h_bitand {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = BitAnd::bitand(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_bitand!(ct_fix__HC__bitand__u8__N16, u8, 16);
emit_h_bitand!(ct_fix__HC__bitand__u16__N16, u16, 16);
emit_h_bitand!(ct_fix__HC__bitand__u32__N4, u32, 4);
emit_h_bitand!(ct_fix__HC__bitand__u32__N16, u32, 16);
emit_h_bitand!(ct_fix__HC__bitand__u64__N4, u64, 4);

macro_rules! emit_h_bitor {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = BitOr::bitor(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_bitor!(ct_fix__HC__bitor__u8__N16, u8, 16);
emit_h_bitor!(ct_fix__HC__bitor__u16__N16, u16, 16);
emit_h_bitor!(ct_fix__HC__bitor__u32__N4, u32, 4);
emit_h_bitor!(ct_fix__HC__bitor__u32__N16, u32, 16);
emit_h_bitor!(ct_fix__HC__bitor__u64__N4, u64, 4);

macro_rules! emit_h_bitxor {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = BitXor::bitxor(x, y);
            *r.all_limbs()
        });
    };
}
emit_h_bitxor!(ct_fix__HC__bitxor__u8__N16, u8, 16);
emit_h_bitxor!(ct_fix__HC__bitxor__u16__N16, u16, 16);
emit_h_bitxor!(ct_fix__HC__bitxor__u32__N4, u32, 4);
emit_h_bitxor!(ct_fix__HC__bitxor__u32__N16, u32, 16);
emit_h_bitxor!(ct_fix__HC__bitxor__u64__N4, u64, 4);

// Overflowing / wrapping arithmetic (always-CT carry chain). Discard the
// overflow bool; the body's branch-freeness is what we check.
macro_rules! emit_h_overflowing_add {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let (r, _ov) = OverflowingAdd::overflowing_add(&x, &y);
            *r.all_limbs()
        });
    };
}
emit_h_overflowing_add!(ct_fix__HC__overflowing_add__u8__N16, u8, 16);
emit_h_overflowing_add!(ct_fix__HC__overflowing_add__u16__N16, u16, 16);
emit_h_overflowing_add!(ct_fix__HC__overflowing_add__u32__N4, u32, 4);
emit_h_overflowing_add!(ct_fix__HC__overflowing_add__u32__N16, u32, 16);
emit_h_overflowing_add!(ct_fix__HC__overflowing_add__u64__N4, u64, 4);

macro_rules! emit_h_wrapping_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let r = WrappingMul::wrapping_mul(&x, &y);
            *r.all_limbs()
        });
    };
}
emit_h_wrapping_mul!(ct_fix__HC__wrapping_mul__u8__N16, u8, 16);
emit_h_wrapping_mul!(ct_fix__HC__wrapping_mul__u16__N16, u16, 16);
emit_h_wrapping_mul!(ct_fix__HC__wrapping_mul__u32__N4, u32, 4);
emit_h_wrapping_mul!(ct_fix__HC__wrapping_mul__u32__N16, u32, 16);
emit_h_wrapping_mul!(ct_fix__HC__wrapping_mul__u64__N4, u64, 4);

// Carrying add — explicit external carry input, passed as `bool` straight
// through `black_box` (see the FixedUInt fixture note on the AVR wrapper).
macro_rules! emit_h_carrying_add {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            carry: bool,
            out_ptr: *mut [$T; $N],
        ) -> u8 {
            let a_arr = core::hint::black_box(unsafe { *a_ptr });
            let b_arr = core::hint::black_box(unsafe { *b_ptr });
            let c = core::hint::black_box(carry);
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a_arr, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b_arr, $N as u16);
            let (r, co) = CarryingAdd::carrying_add(x, y, c);
            let result = core::hint::black_box(*r.all_limbs());
            unsafe {
                *out_ptr = result;
            }
            core::hint::black_box(co as u8)
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_carrying_add!($name, $T, $N););
    };
}
emit_h_carrying_add!(ct_fix__HC__carrying_add__u8__N16, u8, 16);
emit_h_carrying_add!(ct_fix__HC__carrying_add__u16__N16, u16, 16);
emit_h_carrying_add!(ct_fix__HC__carrying_add__u32__N4, u32, 4);
emit_h_carrying_add!(ct_fix__HC__carrying_add__u32__N16, u32, 16);
emit_h_carrying_add!(ct_fix__HC__carrying_add__u64__N4, u64, 4);

// Ord::cmp — folded to u8 (Less=0xFF, Equal=0, Greater=1).
macro_rules! emit_h_cmp {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            (x.cmp(&y) as i8) as u8
        });
    };
}
emit_h_cmp!(ct_fix__HC__cmp__u8__N16, u8, 16);
emit_h_cmp!(ct_fix__HC__cmp__u16__N16, u16, 16);
emit_h_cmp!(ct_fix__HC__cmp__u32__N4, u32, 4);
emit_h_cmp!(ct_fix__HC__cmp__u32__N16, u32, 16);
emit_h_cmp!(ct_fix__HC__cmp__u64__N4, u64, 4);

// Bit counts: count_ones / swap_bytes / reverse_bits
macro_rules! emit_h_count_ones {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            PrimBits::count_ones(x)
        });
    };
}
emit_h_count_ones!(ct_fix__HC__count_ones__u8__N16, u8, 16);
emit_h_count_ones!(ct_fix__HC__count_ones__u16__N16, u16, 16);
emit_h_count_ones!(ct_fix__HC__count_ones__u32__N4, u32, 4);
emit_h_count_ones!(ct_fix__HC__count_ones__u32__N16, u32, 16);
emit_h_count_ones!(ct_fix__HC__count_ones__u64__N4, u64, 4);

macro_rules! emit_h_swap_bytes {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let r = PrimBits::swap_bytes(x);
            *r.all_limbs()
        });
    };
}
emit_h_swap_bytes!(ct_fix__HC__swap_bytes__u8__N16, u8, 16);
emit_h_swap_bytes!(ct_fix__HC__swap_bytes__u16__N16, u16, 16);
emit_h_swap_bytes!(ct_fix__HC__swap_bytes__u32__N4, u32, 4);
emit_h_swap_bytes!(ct_fix__HC__swap_bytes__u32__N16, u32, 16);
emit_h_swap_bytes!(ct_fix__HC__swap_bytes__u64__N4, u64, 4);

macro_rules! emit_h_reverse_bits {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let r = PrimBits::reverse_bits(x);
            *r.all_limbs()
        });
    };
}
emit_h_reverse_bits!(ct_fix__HC__reverse_bits__u8__N16, u8, 16);
emit_h_reverse_bits!(ct_fix__HC__reverse_bits__u16__N16, u16, 16);
emit_h_reverse_bits!(ct_fix__HC__reverse_bits__u32__N4, u32, 4);
emit_h_reverse_bits!(ct_fix__HC__reverse_bits__u32__N16, u32, 16);
emit_h_reverse_bits!(ct_fix__HC__reverse_bits__u64__N4, u64, 4);

// =============================================================================
// Category HCT: const-num-traits `Ct*` masked-return trait impls.
// =============================================================================

// CtParity::ct_is_odd
macro_rules! emit_h_ct_is_odd {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            x.ct_is_odd().unwrap_u8()
        });
    };
}
emit_h_ct_is_odd!(ct_fix__HCT__ct_is_odd__u8__N16, u8, 16);
emit_h_ct_is_odd!(ct_fix__HCT__ct_is_odd__u16__N16, u16, 16);
emit_h_ct_is_odd!(ct_fix__HCT__ct_is_odd__u32__N4, u32, 4);
emit_h_ct_is_odd!(ct_fix__HCT__ct_is_odd__u32__N16, u32, 16);
emit_h_ct_is_odd!(ct_fix__HCT__ct_is_odd__u64__N4, u64, 4);

// CtIsZero::ct_is_zero
macro_rules! emit_h_ct_is_zero {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            CtIsZero::ct_is_zero(&x).unwrap_u8()
        });
    };
}
emit_h_ct_is_zero!(ct_fix__HCT__ct_is_zero__u8__N16, u8, 16);
emit_h_ct_is_zero!(ct_fix__HCT__ct_is_zero__u16__N16, u16, 16);
emit_h_ct_is_zero!(ct_fix__HCT__ct_is_zero__u32__N4, u32, 4);
emit_h_ct_is_zero!(ct_fix__HCT__ct_is_zero__u32__N16, u32, 16);
emit_h_ct_is_zero!(ct_fix__HCT__ct_is_zero__u64__N4, u64, 4);

// CtIsPowerOfTwo::ct_is_power_of_two
macro_rules! emit_h_ct_is_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            x.ct_is_power_of_two().unwrap_u8()
        });
    };
}
emit_h_ct_is_pow2!(ct_fix__HCT__ct_is_pow2__u8__N16, u8, 16);
emit_h_ct_is_pow2!(ct_fix__HCT__ct_is_pow2__u16__N16, u16, 16);
emit_h_ct_is_pow2!(ct_fix__HCT__ct_is_pow2__u32__N4, u32, 4);
emit_h_ct_is_pow2!(ct_fix__HCT__ct_is_pow2__u32__N16, u32, 16);
emit_h_ct_is_pow2!(ct_fix__HCT__ct_is_pow2__u64__N4, u64, 4);

// CtCheckedAdd / CtCheckedSub / CtCheckedMul (CtOption-returning)
macro_rules! emit_h_ct_checked_add {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let res = <HeaplessBigInt<$T, $N, Ct> as CtCheckedAdd>::ct_checked_add(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(HeaplessBigInt::<$T, $N, Ct>::from_limbs([0; $N], $N as u16));
            (*value.all_limbs(), valid)
        });
    };
}
emit_h_ct_checked_add!(ct_fix__HCT__ct_checked_add__u8__N16, u8, 16);
emit_h_ct_checked_add!(ct_fix__HCT__ct_checked_add__u16__N16, u16, 16);
emit_h_ct_checked_add!(ct_fix__HCT__ct_checked_add__u32__N4, u32, 4);
emit_h_ct_checked_add!(ct_fix__HCT__ct_checked_add__u32__N16, u32, 16);
emit_h_ct_checked_add!(ct_fix__HCT__ct_checked_add__u64__N4, u64, 4);

macro_rules! emit_h_ct_checked_sub {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let res = <HeaplessBigInt<$T, $N, Ct> as CtCheckedSub>::ct_checked_sub(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(HeaplessBigInt::<$T, $N, Ct>::from_limbs([0; $N], $N as u16));
            (*value.all_limbs(), valid)
        });
    };
}
emit_h_ct_checked_sub!(ct_fix__HCT__ct_checked_sub__u8__N16, u8, 16);
emit_h_ct_checked_sub!(ct_fix__HCT__ct_checked_sub__u16__N16, u16, 16);
emit_h_ct_checked_sub!(ct_fix__HCT__ct_checked_sub__u32__N4, u32, 4);
emit_h_ct_checked_sub!(ct_fix__HCT__ct_checked_sub__u32__N16, u32, 16);
emit_h_ct_checked_sub!(ct_fix__HCT__ct_checked_sub__u64__N4, u64, 4);

macro_rules! emit_h_ct_checked_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let y = HeaplessBigInt::<$T, $N, Ct>::from_limbs(b, $N as u16);
            let res = <HeaplessBigInt<$T, $N, Ct> as CtCheckedMul>::ct_checked_mul(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(HeaplessBigInt::<$T, $N, Ct>::from_limbs([0; $N], $N as u16));
            (*value.all_limbs(), valid)
        });
    };
}
emit_h_ct_checked_mul!(ct_fix__HCT__ct_checked_mul__u8__N16, u8, 16);
emit_h_ct_checked_mul!(ct_fix__HCT__ct_checked_mul__u16__N16, u16, 16);
emit_h_ct_checked_mul!(ct_fix__HCT__ct_checked_mul__u32__N4, u32, 4);
emit_h_ct_checked_mul!(ct_fix__HCT__ct_checked_mul__u32__N16, u32, 16);
emit_h_ct_checked_mul!(ct_fix__HCT__ct_checked_mul__u64__N4, u64, 4);

// CtNonZero::into_nonzero_ct (CtOption<NonZeroHeaplessBigInt>). Project to the
// inner value via `CtOption::map(|nz| nz.get())` before materializing, so we
// never construct a default `NonZeroHeaplessBigInt` (mirrors the FixedUInt
// fixture's approach).
macro_rules! emit_h_into_nonzero_ct {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_un!($name, $T, $N, |a| {
            let x = HeaplessBigInt::<$T, $N, Ct>::from_limbs(a, $N as u16);
            let res = <HeaplessBigInt<$T, $N, Ct> as CtNonZero>::into_nonzero_ct(x);
            let valid = res.is_some().unwrap_u8();
            let inner: subtle::CtOption<HeaplessBigInt<$T, $N, Ct>> = res.map(|nz| nz.get());
            let value =
                inner.unwrap_or(HeaplessBigInt::<$T, $N, Ct>::from_limbs([0; $N], $N as u16));
            (*value.all_limbs(), valid)
        });
    };
}
emit_h_into_nonzero_ct!(ct_fix__HCT__into_nonzero_ct__u8__N16, u8, 16);
emit_h_into_nonzero_ct!(ct_fix__HCT__into_nonzero_ct__u16__N16, u16, 16);
emit_h_into_nonzero_ct!(ct_fix__HCT__into_nonzero_ct__u32__N4, u32, 4);
emit_h_into_nonzero_ct!(ct_fix__HCT__into_nonzero_ct__u32__N16, u32, 16);
emit_h_into_nonzero_ct!(ct_fix__HCT__into_nonzero_ct__u64__N4, u64, 4);
