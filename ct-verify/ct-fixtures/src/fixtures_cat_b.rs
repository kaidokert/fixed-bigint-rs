//! Category B: Ct-only direct impls. These methods don't exist on Nct.
//!
//! Includes the inherent `ct_checked_*` methods, the four `subtle::*`
//! trait impls, and `forget_ct` (the Ct → Nct explicit downgrade).

use fixed_bigint::{Ct, FixedUInt, Nct};
use subtle::{ConditionallySelectable, ConstantTimeEq, ConstantTimeGreater, ConstantTimeLess};

use crate::{
    ct_fix_bin, ct_fix_checked_bin, ct_fix_checked_scalar, ct_fix_checked_un, ct_fix_pred,
    ct_fix_pred2, ct_fix_un,
};

// =============================================================================
// subtle::ConstantTimeEq / ConstantTimeGreater / ConstantTimeLess on Ct
// =============================================================================

macro_rules! emit_ct_eq {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            x.ct_eq(&y).unwrap_u8()
        });
    };
}
emit_ct_eq!(ct_fix__B__ct_eq__u8__N16, u8, 16);
emit_ct_eq!(ct_fix__B__ct_eq__u16__N16, u16, 16);
emit_ct_eq!(ct_fix__B__ct_eq__u32__N4, u32, 4);
emit_ct_eq!(ct_fix__B__ct_eq__u32__N16, u32, 16);
emit_ct_eq!(ct_fix__B__ct_eq__u64__N4, u64, 4);

macro_rules! emit_ct_gt {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            x.ct_gt(&y).unwrap_u8()
        });
    };
}
emit_ct_gt!(ct_fix__B__ct_gt__u8__N16, u8, 16);
emit_ct_gt!(ct_fix__B__ct_gt__u16__N16, u16, 16);
emit_ct_gt!(ct_fix__B__ct_gt__u32__N4, u32, 4);
emit_ct_gt!(ct_fix__B__ct_gt__u32__N16, u32, 16);
emit_ct_gt!(ct_fix__B__ct_gt__u64__N4, u64, 4);

macro_rules! emit_ct_lt {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred2!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            x.ct_lt(&y).unwrap_u8()
        });
    };
}
emit_ct_lt!(ct_fix__B__ct_lt__u8__N16, u8, 16);
emit_ct_lt!(ct_fix__B__ct_lt__u16__N16, u16, 16);
emit_ct_lt!(ct_fix__B__ct_lt__u32__N4, u32, 4);
emit_ct_lt!(ct_fix__B__ct_lt__u32__N16, u32, 16);
emit_ct_lt!(ct_fix__B__ct_lt__u64__N4, u64, 4);

// =============================================================================
// subtle::ConditionallySelectable::conditional_select on Ct
//
// Different signature: takes a Choice. We pass an extra u8 (0 or 1) as
// the third arg, convert to Choice inside.
// =============================================================================

macro_rules! emit_cond_select {
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
            let x = FixedUInt::<$T, $N, Ct>::from(a_arr);
            let y = FixedUInt::<$T, $N, Ct>::from(b_arr);
            let r = FixedUInt::<$T, $N, Ct>::conditional_select(&x, &y, subtle::Choice::from(c));
            let result = core::hint::black_box(*r.words());
            unsafe {
                *out_ptr = result;
            }
        }
    };
}
emit_cond_select!(ct_fix__B__cond_select__u8__N16, u8, 16);
emit_cond_select!(ct_fix__B__cond_select__u16__N16, u16, 16);
emit_cond_select!(ct_fix__B__cond_select__u32__N4, u32, 4);
emit_cond_select!(ct_fix__B__cond_select__u32__N16, u32, 16);
emit_cond_select!(ct_fix__B__cond_select__u64__N4, u64, 4);

// =============================================================================
// ct_checked_add / sub / mul (Phase 3j)
// =============================================================================

macro_rules! emit_ct_checked_add {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = x.ct_checked_add(&y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_add!(ct_fix__B__ct_checked_add__u8__N16, u8, 16);
emit_ct_checked_add!(ct_fix__B__ct_checked_add__u16__N16, u16, 16);
emit_ct_checked_add!(ct_fix__B__ct_checked_add__u32__N4, u32, 4);
emit_ct_checked_add!(ct_fix__B__ct_checked_add__u32__N16, u32, 16);
emit_ct_checked_add!(ct_fix__B__ct_checked_add__u64__N4, u64, 4);

macro_rules! emit_ct_checked_sub {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = x.ct_checked_sub(&y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_sub!(ct_fix__B__ct_checked_sub__u8__N16, u8, 16);
emit_ct_checked_sub!(ct_fix__B__ct_checked_sub__u16__N16, u16, 16);
emit_ct_checked_sub!(ct_fix__B__ct_checked_sub__u32__N4, u32, 4);
emit_ct_checked_sub!(ct_fix__B__ct_checked_sub__u32__N16, u32, 16);
emit_ct_checked_sub!(ct_fix__B__ct_checked_sub__u64__N4, u64, 4);

macro_rules! emit_ct_checked_mul {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = x.ct_checked_mul(&y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_mul!(ct_fix__B__ct_checked_mul__u8__N16, u8, 16);
emit_ct_checked_mul!(ct_fix__B__ct_checked_mul__u16__N16, u16, 16);
emit_ct_checked_mul!(ct_fix__B__ct_checked_mul__u32__N4, u32, 4);
emit_ct_checked_mul!(ct_fix__B__ct_checked_mul__u32__N16, u32, 16);
emit_ct_checked_mul!(ct_fix__B__ct_checked_mul__u64__N4, u64, 4);

// =============================================================================
// ct_checked_shl / shr / pow (Phase 3k / 3l)
// =============================================================================

macro_rules! emit_ct_checked_shl {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_scalar!($name, $T, $N, u32, |a, s| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let res = x.ct_checked_shl(s);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_shl!(ct_fix__B__ct_checked_shl__u8__N16, u8, 16);
emit_ct_checked_shl!(ct_fix__B__ct_checked_shl__u16__N16, u16, 16);
emit_ct_checked_shl!(ct_fix__B__ct_checked_shl__u32__N4, u32, 4);
emit_ct_checked_shl!(ct_fix__B__ct_checked_shl__u32__N16, u32, 16);
emit_ct_checked_shl!(ct_fix__B__ct_checked_shl__u64__N4, u64, 4);

macro_rules! emit_ct_checked_shr {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_scalar!($name, $T, $N, u32, |a, s| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let res = x.ct_checked_shr(s);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_shr!(ct_fix__B__ct_checked_shr__u8__N16, u8, 16);
emit_ct_checked_shr!(ct_fix__B__ct_checked_shr__u16__N16, u16, 16);
emit_ct_checked_shr!(ct_fix__B__ct_checked_shr__u32__N4, u32, 4);
emit_ct_checked_shr!(ct_fix__B__ct_checked_shr__u32__N16, u32, 16);
emit_ct_checked_shr!(ct_fix__B__ct_checked_shr__u64__N4, u64, 4);

macro_rules! emit_ct_checked_pow {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_scalar!($name, $T, $N, u32, |a, e| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let res = x.ct_checked_pow(e);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_pow!(ct_fix__B__ct_checked_pow__u8__N16, u8, 16);
emit_ct_checked_pow!(ct_fix__B__ct_checked_pow__u16__N16, u16, 16);
emit_ct_checked_pow!(ct_fix__B__ct_checked_pow__u32__N4, u32, 4);
emit_ct_checked_pow!(ct_fix__B__ct_checked_pow__u32__N16, u32, 16);
emit_ct_checked_pow!(ct_fix__B__ct_checked_pow__u64__N4, u64, 4);

// =============================================================================
// ct_checked_next_power_of_two (Phase 3m)
// =============================================================================

macro_rules! emit_ct_checked_npot {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let res = x.ct_checked_next_power_of_two();
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_npot!(ct_fix__B__ct_checked_npot__u8__N16, u8, 16);
emit_ct_checked_npot!(ct_fix__B__ct_checked_npot__u16__N16, u16, 16);
emit_ct_checked_npot!(ct_fix__B__ct_checked_npot__u32__N4, u32, 4);
emit_ct_checked_npot!(ct_fix__B__ct_checked_npot__u32__N16, u32, 16);
emit_ct_checked_npot!(ct_fix__B__ct_checked_npot__u64__N4, u64, 4);

// =============================================================================
// forget_ct: trivially branch-free (it's a memcpy / from_array), but
// include it as a regression watch in case someone adds a debug_assert.
// =============================================================================

macro_rules! emit_forget_ct {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let n: FixedUInt<$T, $N, Nct> = x.forget_ct();
            *n.words()
        });
    };
}
emit_forget_ct!(ct_fix__B__forget_ct__u8__N16, u8, 16);
emit_forget_ct!(ct_fix__B__forget_ct__u16__N16, u16, 16);
emit_forget_ct!(ct_fix__B__forget_ct__u32__N4, u32, 4);
emit_forget_ct!(ct_fix__B__forget_ct__u32__N16, u32, 16);
emit_forget_ct!(ct_fix__B__forget_ct__u64__N4, u64, 4);
