//! Registrations for the category ASYM fixtures defined in ct-fixtures.
//!
//! Each fixture here taints only its single secret-slot input (the shift
//! amount, the choice byte, or the exponent), leaves the rest of the
//! computation involving hardcoded constants on the symbol side, and
//! invokes the corresponding `ct_fix__ASYM__*` symbol from ct-fixtures.
//!
//! These exist as a regression test for the load-bearing `black_box`
//! calls in `const_shl_ct`, `const_ct_select`, and `ct_checked_pow` —
//! see the matching `fixtures_asym.rs` in ct-fixtures for the
//! per-fixture rationale.

// =============================================================================
// Asymmetric shift: tainted u32 amount → output array.
// =============================================================================

macro_rules! ctgrind_asym_shl_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(amount: *const u32, out: *mut [$T; $N]);
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let amount: u32 = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint_val(&amount);
                unsafe { $name(&amount, &mut out); }
                $crate::macros::untaint(&out);
                let _ = ::core::hint::black_box(out);
            }
            inventory::submit! {
                $crate::Fixture {
                    name: stringify!($name),
                    run: [<run_ $name>],
                }
            }
        }
    };
}

ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u8__N16, u8, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u16__N16, u16, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u32__N4, u32, 4);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u32__N16, u32, 16);
ctgrind_asym_shl_u32!(ct_fix__ASYM__one_shl__u64__N4, u64, 4);

// =============================================================================
// Asymmetric conditional_select: tainted u8 choice → output array.
// =============================================================================

macro_rules! ctgrind_asym_select_u8 {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(choice: *const u8, out: *mut [$T; $N]);
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let choice: u8 = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint_val(&choice);
                unsafe { $name(&choice, &mut out); }
                $crate::macros::untaint(&out);
                let _ = ::core::hint::black_box(out);
            }
            inventory::submit! {
                $crate::Fixture {
                    name: stringify!($name),
                    run: [<run_ $name>],
                }
            }
        }
    };
}

ctgrind_asym_select_u8!(ct_fix__ASYM__cond_select_consts__u8__N16, u8, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__cond_select_consts__u16__N16, u16, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__cond_select_consts__u32__N4, u32, 4);
ctgrind_asym_select_u8!(ct_fix__ASYM__cond_select_consts__u32__N16, u32, 16);
ctgrind_asym_select_u8!(ct_fix__ASYM__cond_select_consts__u64__N4, u64, 4);

// =============================================================================
// Asymmetric pow: tainted u32 exponent → output array + validity u8.
// =============================================================================

macro_rules! ctgrind_asym_pow_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(exp: *const u32, out: *mut [$T; $N]) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let exp: u32 = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint_val(&exp);
                let r = unsafe { $name(&exp, &mut out) };
                $crate::macros::untaint(&out);
                $crate::macros::untaint_val(&r);
                let _ = ::core::hint::black_box(out);
                let _ = ::core::hint::black_box(r);
            }
            inventory::submit! {
                $crate::Fixture {
                    name: stringify!($name),
                    run: [<run_ $name>],
                }
            }
        }
    };
}

ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u8__N16, u8, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u16__N16, u16, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u32__N4, u32, 4);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u32__N16, u32, 16);
ctgrind_asym_pow_u32!(ct_fix__ASYM__pow_const_base__u64__N4, u64, 4);
