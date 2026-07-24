//! Inspection fixtures for the fixed-bigint CT-verify harness.
//!
//! Each fixture is a `#[no_mangle] pub extern "C"` symbol that exercises
//! one Ct primitive at one concrete `(T, N)` instantiation. The driver
//! crate (`ct-driver`) cross-builds this library for each target in the
//! priority list, disassembles the resulting archive, and grep-checks
//! every `ct_fix__*` symbol for forbidden conditional-control-transfer
//! mnemonics.
//!
//! # Naming
//!
//! `ct_fix__<cat>__<op>__<T>__N<n>` — `cat` ∈ {A, B, C}, `op` is a short
//! operation tag, `T` is the limb word type, `N` is the limb count.
//!
//! Negative controls deliberately exercise Nct primitives that MUST trip
//! the gate; they use the `nct_fix__neg__*` prefix so the driver can
//! distinguish them and assert each one produces ≥ 1 violation.

// `no_std` is gated on the `panic-handler` feature so host-side consumers
// (ct-ctgrind) can link this crate as an rlib alongside std, which supplies
// the panic handler and eh personality that bare-metal builds lack.
#![cfg_attr(feature = "panic-handler", no_std)]
#![allow(non_snake_case)]
#![cfg_attr(not(test), allow(unused_imports))]

mod fixtures_asym;
mod fixtures_cat_a;
mod fixtures_cat_b;
mod fixtures_cat_c;
mod fixtures_ct_traits;
mod fixtures_neg;

/// No-op Rust-visible anchor. Host-side consumers (ct-ctgrind) call this
/// once so rustc actually links the rlib at all — without a Rust-side
/// reference it would be dropped from the link line and the
/// `#[no_mangle] extern "C"` fixture symbols would resolve as undefined.
pub fn link_anchor() {}

// Only define a panic_handler under the `panic-handler` feature (default on).
// When this crate is linked as an rlib into a host binary (ct-ctgrind etc.),
// std supplies its own and the two would otherwise collide; that consumer
// disables the default features.
#[cfg(feature = "panic-handler")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// =============================================================================
// Fixture macros. Every fixture in this crate is one of these shapes.
// =============================================================================

/// Binary fixture: (T,N) × (T,N) → (T,N).
///
/// Used for: arithmetic ops (sat_add/sub/mul, ct_eq stored as out array,
/// ct_gt/lt stored as scalar), bitwise ops (and/or/xor), wrapping/over-
/// flowing arithmetic that doesn't need the overflow bit separately, etc.
#[macro_export]
macro_rules! ct_fix_bin {
    ($name:ident, $T:ty, $N:literal, |$a:ident, $b:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            out_ptr: *mut [$T; $N],
        ) {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let $b = core::hint::black_box(unsafe { *b_ptr });
            let result: [$T; $N] = $body;
            let result = core::hint::black_box(result);
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_bin!($name, $T, $N););
    };
}

/// Unary fixture: (T,N) → (T,N).
///
/// Used for: not, reverse_bits, swap_bytes, to_be/le, from_be/le,
/// is_power_of_two→out_zero/one (we encode as array; the predicate
/// variant `ct_fix_pred` is preferred when the output is just a bool).
#[macro_export]
macro_rules! ct_fix_un {
    ($name:ident, $T:ty, $N:literal, |$a:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N], out_ptr: *mut [$T; $N]) {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let result: [$T; $N] = $body;
            let result = core::hint::black_box(result);
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_un!($name, $T, $N););
    };
}

/// Predicate fixture: (T,N) → u8.
///
/// Used for: is_zero, is_one, is_power_of_two — and for ct_eq/ct_gt/ct_lt
/// when the test wants the Choice return type folded to u8 via
/// `.unwrap_u8()`. Output is always wrapped in black_box.
#[macro_export]
macro_rules! ct_fix_pred {
    ($name:ident, $T:ty, $N:literal, |$a:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N]) -> u8 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let result: u8 = $body;
            core::hint::black_box(result)
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_pred!($name, $T, $N););
    };
}

/// Binary predicate fixture: (T,N) × (T,N) → u8.
#[macro_export]
macro_rules! ct_fix_pred2 {
    ($name:ident, $T:ty, $N:literal, |$a:ident, $b:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N], b_ptr: *const [$T; $N]) -> u8 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let $b = core::hint::black_box(unsafe { *b_ptr });
            let result: u8 = $body;
            core::hint::black_box(result)
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_pred2!($name, $T, $N););
    };
}

/// Bit-count fixture: (T,N) → u32.
///
/// Used for: count_ones, count_zeros, leading_zeros, trailing_zeros,
/// bit_length.
#[macro_export]
macro_rules! ct_fix_count {
    ($name:ident, $T:ty, $N:literal, |$a:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N]) -> u32 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let result: u32 = $body;
            core::hint::black_box(result)
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_count!($name, $T, $N););
    };
}

/// Shift fixture: (T,N) × scalar → (T,N).
///
/// Used for: shl, shr (variable-amount shift), unbounded_shl/shr.
/// `$NT` is `usize` for Shl<usize>/Shr<usize> or `u32` for the
/// Unbounded variants.
#[macro_export]
macro_rules! ct_fix_shift {
    ($name:ident, $T:ty, $N:literal, $NT:ty, |$a:ident, $n:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N], n_val: $NT, out_ptr: *mut [$T; $N]) {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let $n = core::hint::black_box(n_val);
            let result: [$T; $N] = $body;
            let result = core::hint::black_box(result);
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_shift!($name, $T, $N, $NT););
    };
}

/// Checked-binary fixture: (T,N) × (T,N) → (T,N) + u8 validity.
///
/// Used for: `ct_checked_add/sub/mul`. The CtOption is split into the
/// always-defined value (written to `out_ptr`) and the validity Choice
/// (returned as u8). Both are wrapped in black_box.
#[macro_export]
macro_rules! ct_fix_checked_bin {
    ($name:ident, $T:ty, $N:literal, |$a:ident, $b:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(
            a_ptr: *const [$T; $N],
            b_ptr: *const [$T; $N],
            out_ptr: *mut [$T; $N],
        ) -> u8 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let $b = core::hint::black_box(unsafe { *b_ptr });
            let (value, valid): ([$T; $N], u8) = $body;
            let value = core::hint::black_box(value);
            let valid = core::hint::black_box(valid);
            unsafe {
                *out_ptr = value;
            }
            valid
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_checked_bin!($name, $T, $N););
    };
}

/// Checked-unary-with-scalar fixture: (T,N) × u32 → (T,N) + u8 validity.
///
/// Used for: `ct_checked_shl/shr` (the scalar is u32 bits) and
/// `ct_checked_pow` (the scalar is u32 exp).
#[macro_export]
macro_rules! ct_fix_checked_scalar {
    ($name:ident, $T:ty, $N:literal, $ST:ty, |$a:ident, $s:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N], s_val: $ST, out_ptr: *mut [$T; $N]) -> u8 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let $s = core::hint::black_box(s_val);
            let (value, valid): ([$T; $N], u8) = $body;
            let value = core::hint::black_box(value);
            let valid = core::hint::black_box(valid);
            unsafe {
                *out_ptr = value;
            }
            valid
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_checked_scalar!($name, $T, $N, $ST););
    };
}

/// Checked-unary fixture: (T,N) → (T,N) + u8 validity.
///
/// Used for: `ct_checked_next_power_of_two`.
#[macro_export]
macro_rules! ct_fix_checked_un {
    ($name:ident, $T:ty, $N:literal, |$a:ident| $body:block) => {
        #[no_mangle]
        pub extern "C" fn $name(a_ptr: *const [$T; $N], out_ptr: *mut [$T; $N]) -> u8 {
            let $a = core::hint::black_box(unsafe { *a_ptr });
            let (value, valid): ([$T; $N], u8) = $body;
            let value = core::hint::black_box(value);
            let valid = core::hint::black_box(valid);
            unsafe {
                *out_ptr = value;
            }
            valid
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_checked_un!($name, $T, $N););
    };
}
