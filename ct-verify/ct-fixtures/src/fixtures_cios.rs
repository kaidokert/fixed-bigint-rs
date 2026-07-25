//! `modmath_cios::CiosRowOps` constant-time fixtures — the Montgomery
//! multiply-accumulate row kernels that drive CIOS modular multiplication.
//!
//! Behind the `cios` cargo feature (which enables `fixed-bigint/cios`). Both
//! `mul_acc_row` (Phase 1) and `mul_acc_shift_row` (Phase 2) are exercised on
//! both carriers. The ops are always-CT by construction (one body generic over
//! `P`, loops bounded on the public `N`/`len`), so they're regression-watch:
//! pinned so a future change — like the `if top_hi_bit` that heapless
//! `mul_acc_shift_row` used to carry — can't reintroduce a secret-dependent
//! branch.
//!
//! ABI: `(mult, acc, scalar, carry) → acc' + carry_word`. The two single-limb
//! `T` scalars are secret inputs; `acc` is written to `out`, the carry word is
//! returned. Uses the `fbx_ctgrind_mul_acc` shape.

use const_num_traits::Ct;
use fixed_bigint::FixedUInt;
use modmath_cios::CiosRowOps;

// ── FixedUInt (Category C) ──

macro_rules! emit_cios_mul_acc_row {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            mult_ptr: *const [$T; $N],
            acc_ptr: *const [$T; $N],
            scalar: $T,
            carry: $T,
            out_ptr: *mut [$T; $N],
        ) -> $T {
            let mult_arr = core::hint::black_box(unsafe { *mult_ptr });
            let acc_arr = core::hint::black_box(unsafe { *acc_ptr });
            let s = core::hint::black_box(scalar);
            let c = core::hint::black_box(carry);
            let mult = FixedUInt::<$T, $N, Ct>::from(mult_arr);
            let acc = FixedUInt::<$T, $N, Ct>::from(acc_arr);
            let (acc, cout) = crate::catalog::cios_mul_acc_row(s, mult, acc, c);
            unsafe {
                *out_ptr = core::hint::black_box(*acc.words());
            }
            core::hint::black_box(cout)
        }
        #[cfg(feature = "ctgrind")]
        fbx_ctgrind_mul_acc!($name, $T, $N);
    };
}
emit_cios_mul_acc_row!(ct_fix__C__cios_mul_acc_row__u8__N16, u8, 16);
emit_cios_mul_acc_row!(ct_fix__C__cios_mul_acc_row__u32__N4, u32, 4);
emit_cios_mul_acc_row!(ct_fix__C__cios_mul_acc_row__u32__N16, u32, 16);
emit_cios_mul_acc_row!(ct_fix__C__cios_mul_acc_row__u64__N4, u64, 4);

macro_rules! emit_cios_mul_acc_shift_row {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(
            mult_ptr: *const [$T; $N],
            acc_ptr: *const [$T; $N],
            scalar: $T,
            acc_hi: $T,
            out_ptr: *mut [$T; $N],
        ) -> $T {
            let mult_arr = core::hint::black_box(unsafe { *mult_ptr });
            let acc_arr = core::hint::black_box(unsafe { *acc_ptr });
            let s = core::hint::black_box(scalar);
            let hi = core::hint::black_box(acc_hi);
            let mult = FixedUInt::<$T, $N, Ct>::from(mult_arr);
            let acc = FixedUInt::<$T, $N, Ct>::from(acc_arr);
            let (acc, cout) = crate::catalog::cios_mul_acc_shift_row(s, mult, acc, hi);
            unsafe {
                *out_ptr = core::hint::black_box(*acc.words());
            }
            core::hint::black_box(cout)
        }
        #[cfg(feature = "ctgrind")]
        fbx_ctgrind_mul_acc!($name, $T, $N);
    };
}
emit_cios_mul_acc_shift_row!(ct_fix__C__cios_mul_acc_shift_row__u8__N16, u8, 16);
emit_cios_mul_acc_shift_row!(ct_fix__C__cios_mul_acc_shift_row__u32__N4, u32, 4);
emit_cios_mul_acc_shift_row!(ct_fix__C__cios_mul_acc_shift_row__u32__N16, u32, 16);
emit_cios_mul_acc_shift_row!(ct_fix__C__cios_mul_acc_shift_row__u64__N4, u64, 4);

// ── HeaplessBigInt (Category HC) ──

#[cfg(feature = "heapless")]
mod heapless_cios {
    use super::*;
    use fixed_bigint::HeaplessBigInt;

    macro_rules! emit_h_cios_mul_acc_row {
        ($name:ident, $T:ty, $N:literal) => {
            #[no_mangle]
            pub extern "C" fn $name(
                mult_ptr: *const [$T; $N],
                acc_ptr: *const [$T; $N],
                scalar: $T,
                carry: $T,
                out_ptr: *mut [$T; $N],
            ) -> $T {
                let mult_arr = core::hint::black_box(unsafe { *mult_ptr });
                let acc_arr = core::hint::black_box(unsafe { *acc_ptr });
                let s = core::hint::black_box(scalar);
                let c = core::hint::black_box(carry);
                let mult = HeaplessBigInt::<$T, $N, Ct>::from_limbs(mult_arr, $N as u16);
                let acc = HeaplessBigInt::<$T, $N, Ct>::from_limbs(acc_arr, $N as u16);
                let (acc, cout) = crate::catalog::cios_mul_acc_row(s, mult, acc, c);
                unsafe {
                    *out_ptr = core::hint::black_box(*acc.all_limbs());
                }
                core::hint::black_box(cout)
            }
            #[cfg(feature = "ctgrind")]
            fbx_ctgrind_mul_acc!($name, $T, $N);
        };
    }
    emit_h_cios_mul_acc_row!(ct_fix__HC__cios_mul_acc_row__u8__N16, u8, 16);
    emit_h_cios_mul_acc_row!(ct_fix__HC__cios_mul_acc_row__u32__N4, u32, 4);
    emit_h_cios_mul_acc_row!(ct_fix__HC__cios_mul_acc_row__u32__N16, u32, 16);
    emit_h_cios_mul_acc_row!(ct_fix__HC__cios_mul_acc_row__u64__N4, u64, 4);

    macro_rules! emit_h_cios_mul_acc_shift_row {
        ($name:ident, $T:ty, $N:literal) => {
            #[no_mangle]
            pub extern "C" fn $name(
                mult_ptr: *const [$T; $N],
                acc_ptr: *const [$T; $N],
                scalar: $T,
                acc_hi: $T,
                out_ptr: *mut [$T; $N],
            ) -> $T {
                let mult_arr = core::hint::black_box(unsafe { *mult_ptr });
                let acc_arr = core::hint::black_box(unsafe { *acc_ptr });
                let s = core::hint::black_box(scalar);
                let hi = core::hint::black_box(acc_hi);
                let mult = HeaplessBigInt::<$T, $N, Ct>::from_limbs(mult_arr, $N as u16);
                let acc = HeaplessBigInt::<$T, $N, Ct>::from_limbs(acc_arr, $N as u16);
                let (acc, cout) = crate::catalog::cios_mul_acc_shift_row(s, mult, acc, hi);
                unsafe {
                    *out_ptr = core::hint::black_box(*acc.all_limbs());
                }
                core::hint::black_box(cout)
            }
            #[cfg(feature = "ctgrind")]
            fbx_ctgrind_mul_acc!($name, $T, $N);
        };
    }
    emit_h_cios_mul_acc_shift_row!(ct_fix__HC__cios_mul_acc_shift_row__u8__N16, u8, 16);
    emit_h_cios_mul_acc_shift_row!(ct_fix__HC__cios_mul_acc_shift_row__u32__N4, u32, 4);
    emit_h_cios_mul_acc_shift_row!(ct_fix__HC__cios_mul_acc_shift_row__u32__N16, u32, 16);
    emit_h_cios_mul_acc_shift_row!(ct_fix__HC__cios_mul_acc_shift_row__u64__N4, u64, 4);
}
