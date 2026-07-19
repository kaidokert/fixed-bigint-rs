//! Category ASYM: asymmetric-taint regression fixtures.
//!
//! Each fixture here exercises a load-bearing `core::hint::black_box`
//! protection under the *asymmetric* taint pattern that originally
//! surfaced the bugs the `black_box` calls defend against (see PR #118,
//! PR #120 for the address-select / cmov-on-tainted-flag class).
//!
//! Why these are necessary on top of the symmetric Cat A/B/C fixtures: when
//! both operands of the LLVM-rewritten select are tainted, Valgrind sees
//! taint propagation through `cmov`/`csel` without flagging — both possible
//! result values contain tainted bytes, so reading either is correct from
//! Memcheck's POV. The asymmetric case (one operand tainted, one a hardcoded
//! constant) is the configuration that actually surfaces the rewrite:
//! Valgrind sees a `cmov` whose flag depends on a tainted condition while
//! the source operands carry different taint metadata, which is exactly the
//! "use of uninitialised value in conditional move" pattern Memcheck flags.
//!
//! What each family exercises:
//!
//! - `one_shl` — `Self::one() << tainted_amount`. Dispatches through
//!   `Shl<u32>` → `Shl<usize>` → `const_shl_ct`, exercising the
//!   `black_box(bit_k)` in that helper.
//! - `subtle_cond_select` — `subtle::ConditionallySelectable::conditional_select`
//!   on a Ct `FixedUInt` with two non-tainted constant operands. This goes
//!   through subtle's per-limb primitive `T::conditional_select`, NOT our
//!   `const_ct_select` helper — the test target here is subtle's own
//!   `Choice::from(u8)` opacification. Our `const_ct_select`'s `black_box`
//!   protection is already exercised by existing fixtures like
//!   `ct_fix__A__next_pow2__*` and the saturating arithmetic family, which
//!   call `const_ct_select` internally with one tainted operand and one
//!   constant (e.g. `const_ct_select(shifted, max_value, overflow)`).
//! - `pow_const_base` — `const_base.ct_checked_pow(tainted_exp)` with the
//!   base hardcoded to 2. Exercises the per-iteration `black_box(bit)` in
//!   the square-and-multiply inner loop of `ct_checked_pow`.
//!
//! If a future refactor removes one of the protected `black_box` calls,
//! the corresponding fixture trips on the next ctgrind run. They are
//! otherwise expected to pass cleanly on every ctgrind-covered architecture.

use const_num_traits::Ct;
use fixed_bigint::FixedUInt;
use subtle::ConditionallySelectable;

// =============================================================================
// `Self::one() << tainted_amount`
//
// Routes through `Shl<u32>` (which normalises the amount and recurses into
// `Shl<usize>` → `const_shl_ct`), exercising the `black_box(bit_k)` in the
// barrel-shifter inner loop. Non-tainted LHS, tainted shift amount —
// mirrors the configuration that surfaced the original `next_pow2` bug.
// =============================================================================

macro_rules! emit_asym_one_shl {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(amount_ptr: *const u32, out_ptr: *mut [$T; $N]) {
            let amount = core::hint::black_box(unsafe { *amount_ptr });
            let mut one_arr: [$T; $N] = [0; $N];
            one_arr[0] = 1;
            let one = FixedUInt::<$T, $N, Ct>::from(one_arr);
            let shifted = one << amount;
            let result = core::hint::black_box(*shifted.words());
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_asym_shl_u32!($name, $T, $N););
    };
}

emit_asym_one_shl!(ct_fix__ASYM__one_shl__u8__N16, u8, 16);
emit_asym_one_shl!(ct_fix__ASYM__one_shl__u16__N16, u16, 16);
emit_asym_one_shl!(ct_fix__ASYM__one_shl__u32__N4, u32, 4);
emit_asym_one_shl!(ct_fix__ASYM__one_shl__u32__N16, u32, 16);
emit_asym_one_shl!(ct_fix__ASYM__one_shl__u64__N4, u64, 4);

// =============================================================================
// `subtle::ConditionallySelectable::conditional_select(zero, one, tainted_choice)`
//
// Exercises subtle's per-limb primitive `T::conditional_select` and the
// `Choice::from(u8)` opacification it relies on. Note: this does NOT
// reach our internal `const_ct_select` helper — that path runs through
// `next_power_of_two`, `sat_add`/`sat_sub`/`sat_mul`, `abs_diff`,
// `ct_checked_*` shifts, etc., and is exercised by their existing
// fixtures via internal asymmetric flow (e.g. `const_ct_select(shifted,
// max_value, overflow)` where `max_value` is a non-tainted constant).
// =============================================================================

macro_rules! emit_asym_subtle_cond_select {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(choice_ptr: *const u8, out_ptr: *mut [$T; $N]) {
            let choice = core::hint::black_box(unsafe { *choice_ptr });
            let zero = FixedUInt::<$T, $N, Ct>::from([0; $N]);
            let mut one_arr: [$T; $N] = [0; $N];
            one_arr[0] = 1;
            let one = FixedUInt::<$T, $N, Ct>::from(one_arr);
            let selected = FixedUInt::<$T, $N, Ct>::conditional_select(
                &zero,
                &one,
                subtle::Choice::from(choice),
            );
            let result = core::hint::black_box(*selected.words());
            unsafe {
                *out_ptr = result;
            }
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_asym_select_u8!($name, $T, $N););
    };
}

emit_asym_subtle_cond_select!(ct_fix__ASYM__subtle_cond_select__u8__N16, u8, 16);
emit_asym_subtle_cond_select!(ct_fix__ASYM__subtle_cond_select__u16__N16, u16, 16);
emit_asym_subtle_cond_select!(ct_fix__ASYM__subtle_cond_select__u32__N4, u32, 4);
emit_asym_subtle_cond_select!(ct_fix__ASYM__subtle_cond_select__u32__N16, u32, 16);
emit_asym_subtle_cond_select!(ct_fix__ASYM__subtle_cond_select__u64__N4, u64, 4);

// =============================================================================
// `const_base.ct_checked_pow(tainted_exp)` with non-tainted base (= 2).
//
// Exercises `ct_checked_pow`'s `black_box(bit)` in the square-and-multiply
// inner loop. With a non-tainted base, the per-iteration select between
// `result` and `candidate` (both derived from non-tainted state) is what
// the cmov-on-tainted-flag rewrite would target.
// =============================================================================

macro_rules! emit_asym_pow_const_base {
    ($name:ident, $T:ty, $N:literal) => {
        #[no_mangle]
        pub extern "C" fn $name(exp_ptr: *const u32, out_ptr: *mut [$T; $N]) -> u8 {
            let exp = core::hint::black_box(unsafe { *exp_ptr });
            let mut base_arr: [$T; $N] = [0; $N];
            base_arr[0] = 2;
            let base = FixedUInt::<$T, $N, Ct>::from(base_arr);
            let res = base.ct_checked_pow(exp);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(FixedUInt::<$T, $N, Ct>::from([0; $N]));
            let result_words = core::hint::black_box(*value.words());
            let valid = core::hint::black_box(valid);
            unsafe {
                *out_ptr = result_words;
            }
            valid
        }
        #[cfg(feature = "ctgrind")]
        krabi_caliper::ctgrind_local!($name, krabi_caliper::ctgrind_asym_pow_u32!($name, $T, $N););
    };
}

emit_asym_pow_const_base!(ct_fix__ASYM__pow_const_base__u8__N16, u8, 16);
emit_asym_pow_const_base!(ct_fix__ASYM__pow_const_base__u16__N16, u16, 16);
emit_asym_pow_const_base!(ct_fix__ASYM__pow_const_base__u32__N4, u32, 4);
emit_asym_pow_const_base!(ct_fix__ASYM__pow_const_base__u32__N16, u32, 16);
emit_asym_pow_const_base!(ct_fix__ASYM__pow_const_base__u64__N4, u64, 4);
