//! Category A: methods migrated via `match P::TAG` where the Ct arm is a
//! distinct body. Phase 3c–g + 3i–m in the original migration commits.
//!
//! Each op is exercised at five (T, N) diagonals:
//!   (u8, 16), (u16, 16), (u32, 4), (u32, 16), (u64, 4)

use fixed_bigint::const_numtraits::{
    ConstAbsDiff, ConstBitPrimInt, ConstOne, ConstPowerOfTwo, ConstSaturatingAdd,
    ConstSaturatingMul, ConstSaturatingSub, ConstUnboundedShift, ConstZero,
};
use fixed_bigint::{Ct, FixedUInt};

use crate::{ct_fix_bin, ct_fix_count, ct_fix_pred, ct_fix_shift, ct_fix_un};

// =============================================================================
// ConstSaturatingAdd / Sub / Mul
// =============================================================================

macro_rules! emit_sat_add {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstSaturatingAdd::saturating_add(&x, &y);
            *r.words()
        });
    };
}
emit_sat_add!(ct_fix__A__sat_add__u8__N16, u8, 16);
emit_sat_add!(ct_fix__A__sat_add__u16__N16, u16, 16);
emit_sat_add!(ct_fix__A__sat_add__u32__N4, u32, 4);
emit_sat_add!(ct_fix__A__sat_add__u32__N16, u32, 16);
emit_sat_add!(ct_fix__A__sat_add__u64__N4, u64, 4);

macro_rules! emit_sat_sub {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstSaturatingSub::saturating_sub(&x, &y);
            *r.words()
        });
    };
}
emit_sat_sub!(ct_fix__A__sat_sub__u8__N16, u8, 16);
emit_sat_sub!(ct_fix__A__sat_sub__u16__N16, u16, 16);
emit_sat_sub!(ct_fix__A__sat_sub__u32__N4, u32, 4);
emit_sat_sub!(ct_fix__A__sat_sub__u32__N16, u32, 16);
emit_sat_sub!(ct_fix__A__sat_sub__u64__N4, u64, 4);

macro_rules! emit_sat_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstSaturatingMul::saturating_mul(&x, &y);
            *r.words()
        });
    };
}
emit_sat_mul!(ct_fix__A__sat_mul__u8__N16, u8, 16);
emit_sat_mul!(ct_fix__A__sat_mul__u16__N16, u16, 16);
emit_sat_mul!(ct_fix__A__sat_mul__u32__N4, u32, 4);
emit_sat_mul!(ct_fix__A__sat_mul__u32__N16, u32, 16);
emit_sat_mul!(ct_fix__A__sat_mul__u64__N4, u64, 4);

// =============================================================================
// core::ops::Shl<usize> / Shr<usize> (Phase 3e barrel shifter)
// =============================================================================

macro_rules! emit_shl_usize {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = x << n;
            *r.words()
        });
    };
}
emit_shl_usize!(ct_fix__A__shl_usize__u8__N16, u8, 16);
emit_shl_usize!(ct_fix__A__shl_usize__u16__N16, u16, 16);
emit_shl_usize!(ct_fix__A__shl_usize__u32__N4, u32, 4);
emit_shl_usize!(ct_fix__A__shl_usize__u32__N16, u32, 16);
emit_shl_usize!(ct_fix__A__shl_usize__u64__N4, u64, 4);

macro_rules! emit_shr_usize {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, usize, |a, n| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = x >> n;
            *r.words()
        });
    };
}
emit_shr_usize!(ct_fix__A__shr_usize__u8__N16, u8, 16);
emit_shr_usize!(ct_fix__A__shr_usize__u16__N16, u16, 16);
emit_shr_usize!(ct_fix__A__shr_usize__u32__N4, u32, 4);
emit_shr_usize!(ct_fix__A__shr_usize__u32__N16, u32, 16);
emit_shr_usize!(ct_fix__A__shr_usize__u64__N4, u64, 4);

// =============================================================================
// ConstUnboundedShift::unbounded_shl / unbounded_shr (Phase 3i)
// =============================================================================

macro_rules! emit_unbounded_shl {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = ConstUnboundedShift::unbounded_shl(x, n);
            *r.words()
        });
    };
}
emit_unbounded_shl!(ct_fix__A__unbounded_shl__u8__N16, u8, 16);
emit_unbounded_shl!(ct_fix__A__unbounded_shl__u16__N16, u16, 16);
emit_unbounded_shl!(ct_fix__A__unbounded_shl__u32__N4, u32, 4);
emit_unbounded_shl!(ct_fix__A__unbounded_shl__u32__N16, u32, 16);
emit_unbounded_shl!(ct_fix__A__unbounded_shl__u64__N4, u64, 4);

macro_rules! emit_unbounded_shr {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_shift!($name, $T, $N, u32, |a, n| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = ConstUnboundedShift::unbounded_shr(x, n);
            *r.words()
        });
    };
}
emit_unbounded_shr!(ct_fix__A__unbounded_shr__u8__N16, u8, 16);
emit_unbounded_shr!(ct_fix__A__unbounded_shr__u16__N16, u16, 16);
emit_unbounded_shr!(ct_fix__A__unbounded_shr__u32__N4, u32, 4);
emit_unbounded_shr!(ct_fix__A__unbounded_shr__u32__N16, u32, 16);
emit_unbounded_shr!(ct_fix__A__unbounded_shr__u64__N4, u64, 4);

// =============================================================================
// ConstAbsDiff::abs_diff (Phase 3l)
// =============================================================================

macro_rules! emit_abs_diff {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let r = ConstAbsDiff::abs_diff(x, y);
            *r.words()
        });
    };
}
emit_abs_diff!(ct_fix__A__abs_diff__u8__N16, u8, 16);
emit_abs_diff!(ct_fix__A__abs_diff__u16__N16, u16, 16);
emit_abs_diff!(ct_fix__A__abs_diff__u32__N4, u32, 4);
emit_abs_diff!(ct_fix__A__abs_diff__u32__N16, u32, 16);
emit_abs_diff!(ct_fix__A__abs_diff__u64__N4, u64, 4);

// =============================================================================
// ConstPowerOfTwo::is_power_of_two (Phase 3f) — predicate
// =============================================================================

macro_rules! emit_is_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstPowerOfTwo::is_power_of_two(&x) as u8
        });
    };
}
emit_is_pow2!(ct_fix__A__is_pow2__u8__N16, u8, 16);
emit_is_pow2!(ct_fix__A__is_pow2__u16__N16, u16, 16);
emit_is_pow2!(ct_fix__A__is_pow2__u32__N4, u32, 4);
emit_is_pow2!(ct_fix__A__is_pow2__u32__N16, u32, 16);
emit_is_pow2!(ct_fix__A__is_pow2__u64__N4, u64, 4);

// =============================================================================
// ConstPowerOfTwo::next_power_of_two (Phase 3m)
// =============================================================================

macro_rules! emit_next_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let r = ConstPowerOfTwo::next_power_of_two(x);
            *r.words()
        });
    };
}
emit_next_pow2!(ct_fix__A__next_pow2__u8__N16, u8, 16);
emit_next_pow2!(ct_fix__A__next_pow2__u16__N16, u16, 16);
emit_next_pow2!(ct_fix__A__next_pow2__u32__N4, u32, 4);
emit_next_pow2!(ct_fix__A__next_pow2__u32__N16, u32, 16);
emit_next_pow2!(ct_fix__A__next_pow2__u64__N4, u64, 4);

// =============================================================================
// ConstBitPrimInt::leading_zeros / trailing_zeros (Phase 3c/3d)
// =============================================================================

macro_rules! emit_lz {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstBitPrimInt::leading_zeros(x)
        });
    };
}
emit_lz!(ct_fix__A__leading_zeros__u8__N16, u8, 16);
emit_lz!(ct_fix__A__leading_zeros__u16__N16, u16, 16);
emit_lz!(ct_fix__A__leading_zeros__u32__N4, u32, 4);
emit_lz!(ct_fix__A__leading_zeros__u32__N16, u32, 16);
emit_lz!(ct_fix__A__leading_zeros__u64__N4, u64, 4);

macro_rules! emit_tz {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_count!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstBitPrimInt::trailing_zeros(x)
        });
    };
}
emit_tz!(ct_fix__A__trailing_zeros__u8__N16, u8, 16);
emit_tz!(ct_fix__A__trailing_zeros__u16__N16, u16, 16);
emit_tz!(ct_fix__A__trailing_zeros__u32__N4, u32, 4);
emit_tz!(ct_fix__A__trailing_zeros__u32__N16, u32, 16);
emit_tz!(ct_fix__A__trailing_zeros__u64__N4, u64, 4);

// =============================================================================
// ConstZero::is_zero / ConstOne::is_one (Phase 2 / 3a)
// =============================================================================

macro_rules! emit_is_zero {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstZero::is_zero(&x) as u8
        });
    };
}
emit_is_zero!(ct_fix__A__is_zero__u8__N16, u8, 16);
emit_is_zero!(ct_fix__A__is_zero__u16__N16, u16, 16);
emit_is_zero!(ct_fix__A__is_zero__u32__N4, u32, 4);
emit_is_zero!(ct_fix__A__is_zero__u32__N16, u32, 16);
emit_is_zero!(ct_fix__A__is_zero__u64__N4, u64, 4);

macro_rules! emit_is_one {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            ConstOne::is_one(&x) as u8
        });
    };
}
emit_is_one!(ct_fix__A__is_one__u8__N16, u8, 16);
emit_is_one!(ct_fix__A__is_one__u16__N16, u16, 16);
emit_is_one!(ct_fix__A__is_one__u32__N4, u32, 4);
emit_is_one!(ct_fix__A__is_one__u32__N16, u32, 16);
emit_is_one!(ct_fix__A__is_one__u64__N4, u64, 4);
