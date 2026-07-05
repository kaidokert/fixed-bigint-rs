//! Category CT: const-num-traits `Ct*` trait impls on `FixedUInt`.
//!
//! Exercises the seven masked-return trait methods we ship as of
//! `v0.4.0-alpha.3`. Each fixture compiles down to the trait body —
//! which for our impls either delegates to an existing CT primitive
//! (`OverflowingAdd`/`Sub`/`Mul` for the `CtChecked*` family,
//! `subtle::ConstantTimeEq` for the predicates) or composes one with a
//! `Choice`-returning wrapper. The asm-grep gate verifies no
//! conditional-control-transfer mnemonic shows up in any of these
//! symbols.
//!
//! Coverage matrix (T, N):
//!   (u8, 16), (u16, 16), (u32, 4), (u32, 16), (u64, 4)
//!
//! The seven traits:
//!   - `CtParity::ct_is_odd`         (predicate)
//!   - `CtIsZero::ct_is_zero`        (predicate)
//!   - `CtIsPowerOfTwo::ct_is_power_of_two` (predicate)
//!   - `CtCheckedAdd::ct_checked_add`       (CtOption-binary)
//!   - `CtCheckedSub::ct_checked_sub`       (CtOption-binary)
//!   - `CtCheckedMul::ct_checked_mul`       (CtOption-binary)
//!   - `CtNonZero::into_nonzero_ct`         (CtOption-unary, wraps newtype)

use const_num_traits::ops::ct::{
    CtCheckedAdd, CtCheckedMul, CtCheckedSub, CtIsPowerOfTwo, CtIsZero, CtParity,
};
use const_num_traits::{Ct, CtNonZero};
use fixed_bigint::FixedUInt;

use crate::{ct_fix_bin, ct_fix_checked_bin, ct_fix_checked_un, ct_fix_pred};

// =============================================================================
// CtParity::ct_is_odd  (returns Choice → unwrap_u8 for the ABI)
// =============================================================================

macro_rules! emit_ct_is_odd {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            x.ct_is_odd().unwrap_u8()
        });
    };
}
emit_ct_is_odd!(ct_fix__CT__ct_is_odd__u8__N16, u8, 16);
emit_ct_is_odd!(ct_fix__CT__ct_is_odd__u16__N16, u16, 16);
emit_ct_is_odd!(ct_fix__CT__ct_is_odd__u32__N4, u32, 4);
emit_ct_is_odd!(ct_fix__CT__ct_is_odd__u32__N16, u32, 16);
emit_ct_is_odd!(ct_fix__CT__ct_is_odd__u64__N4, u64, 4);

// =============================================================================
// CtIsZero::ct_is_zero
// =============================================================================

macro_rules! emit_ct_is_zero {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            x.ct_is_zero().unwrap_u8()
        });
    };
}
emit_ct_is_zero!(ct_fix__CT__ct_is_zero__u8__N16, u8, 16);
emit_ct_is_zero!(ct_fix__CT__ct_is_zero__u16__N16, u16, 16);
emit_ct_is_zero!(ct_fix__CT__ct_is_zero__u32__N4, u32, 4);
emit_ct_is_zero!(ct_fix__CT__ct_is_zero__u32__N16, u32, 16);
emit_ct_is_zero!(ct_fix__CT__ct_is_zero__u64__N4, u64, 4);

// =============================================================================
// CtIsPowerOfTwo::ct_is_power_of_two
// =============================================================================

macro_rules! emit_ct_is_pow2 {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_pred!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            x.ct_is_power_of_two().unwrap_u8()
        });
    };
}
emit_ct_is_pow2!(ct_fix__CT__ct_is_pow2__u8__N16, u8, 16);
emit_ct_is_pow2!(ct_fix__CT__ct_is_pow2__u16__N16, u16, 16);
emit_ct_is_pow2!(ct_fix__CT__ct_is_pow2__u32__N4, u32, 4);
emit_ct_is_pow2!(ct_fix__CT__ct_is_pow2__u32__N16, u32, 16);
emit_ct_is_pow2!(ct_fix__CT__ct_is_pow2__u64__N4, u64, 4);

// =============================================================================
// CtCheckedAdd / CtCheckedSub / CtCheckedMul  (CtOption-returning)
//
// Materialize the result via `CtOption::unwrap_or(default)` (CT-clean —
// uses ConditionallySelectable internally) and split the validity bit
// out via `Choice::unwrap_u8()`.
// =============================================================================

macro_rules! emit_ct_checked_add_trait {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = <FixedUInt<$T, $N, Ct> as CtCheckedAdd>::ct_checked_add(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_add_trait!(ct_fix__CT__ct_checked_add__u8__N16, u8, 16);
emit_ct_checked_add_trait!(ct_fix__CT__ct_checked_add__u16__N16, u16, 16);
emit_ct_checked_add_trait!(ct_fix__CT__ct_checked_add__u32__N4, u32, 4);
emit_ct_checked_add_trait!(ct_fix__CT__ct_checked_add__u32__N16, u32, 16);
emit_ct_checked_add_trait!(ct_fix__CT__ct_checked_add__u64__N4, u64, 4);

macro_rules! emit_ct_checked_sub_trait {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = <FixedUInt<$T, $N, Ct> as CtCheckedSub>::ct_checked_sub(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_sub_trait!(ct_fix__CT__ct_checked_sub__u8__N16, u8, 16);
emit_ct_checked_sub_trait!(ct_fix__CT__ct_checked_sub__u16__N16, u16, 16);
emit_ct_checked_sub_trait!(ct_fix__CT__ct_checked_sub__u32__N4, u32, 4);
emit_ct_checked_sub_trait!(ct_fix__CT__ct_checked_sub__u32__N16, u32, 16);
emit_ct_checked_sub_trait!(ct_fix__CT__ct_checked_sub__u64__N4, u64, 4);

macro_rules! emit_ct_checked_mul_trait {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_bin!($name, $T, $N, |a, b| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let y = FixedUInt::<$T, $N, Ct>::from(b);
            let res = <FixedUInt<$T, $N, Ct> as CtCheckedMul>::ct_checked_mul(&x, &y);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_ct_checked_mul_trait!(ct_fix__CT__ct_checked_mul__u8__N16, u8, 16);
emit_ct_checked_mul_trait!(ct_fix__CT__ct_checked_mul__u16__N16, u16, 16);
emit_ct_checked_mul_trait!(ct_fix__CT__ct_checked_mul__u32__N4, u32, 4);
emit_ct_checked_mul_trait!(ct_fix__CT__ct_checked_mul__u32__N16, u32, 16);
emit_ct_checked_mul_trait!(ct_fix__CT__ct_checked_mul__u64__N4, u64, 4);

// =============================================================================
// CtNonZero::into_nonzero_ct  (CtOption<NonZeroFixedUInt>)
//
// Don't materialize through `NonZeroFixedUInt` at all — use `CtOption::map`
// to project to the inner `FixedUInt` first (zero-cost — the closure is
// just `nz.get()`), then `unwrap_or(ZERO)` on the resulting
// `CtOption<FixedUInt>`. Avoids constructing a default `NonZeroFixedUInt`
// which would have required either `.unwrap()` (a `cbnz` the gate
// rightly flags) or `new_unchecked` (which is `pub(crate)`).
// =============================================================================

macro_rules! emit_into_nonzero_ct {
    ($name:ident, $T:ty, $N:literal) => {
        ct_fix_checked_un!($name, $T, $N, |a| {
            let x = FixedUInt::<$T, $N, Ct>::from(a);
            let res = <FixedUInt<$T, $N, Ct> as CtNonZero>::into_nonzero_ct(x);
            let valid = res.is_some().unwrap_u8();
            let inner: subtle::CtOption<FixedUInt<$T, $N, Ct>> = res.map(|nz| nz.get());
            let value = inner.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            (*value.words(), valid)
        });
    };
}
emit_into_nonzero_ct!(ct_fix__CT__into_nonzero_ct__u8__N16, u8, 16);
emit_into_nonzero_ct!(ct_fix__CT__into_nonzero_ct__u16__N16, u16, 16);
emit_into_nonzero_ct!(ct_fix__CT__into_nonzero_ct__u32__N4, u32, 4);
emit_into_nonzero_ct!(ct_fix__CT__into_nonzero_ct__u32__N16, u32, 16);
emit_into_nonzero_ct!(ct_fix__CT__into_nonzero_ct__u64__N4, u64, 4);
