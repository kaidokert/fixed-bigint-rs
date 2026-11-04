//! Fixed-bigint's ctgrind ABI adapters — one macro per fixture calling shape.
//!
//! The ABI these describe is ct-fixtures' own (`ct_fix_*`), so the adapters
//! live here rather than in the shared harness. Each expands to
//! `krabi_caliper::ctgrind_fixture!`, which owns the fixture registration; the
//! adapter only supplies the run body: declare the fixture's `extern "C"`
//! signature, taint the secret inputs, call it, untaint the outputs. Nothing
//! here reaches past caliper's public surface (`ctgrind_fixture!` +
//! `taint`/`taint_val`/`untaint`/`untaint_val`).
//!
//! The `extern "C"` decl sits inside the run body so it is scoped to that
//! function, not colliding with the same-named `#[no_mangle]` fixture defined
//! alongside it — the isolation `ctgrind_local!` provides for a top-level decl.
//!
//! Adding a new shape (e.g. a widening `carrying_mul` with two outputs) means
//! adding one macro here; the harness never changes.
//!
//! Every secret must reach the fixture through tainted memory. `taint`/
//! `taint_val` set Valgrind metadata, not memory, and fat LTO inlines most
//! fixtures into their run body, so a plain `&a` to a `[0; N]` local lets the
//! optimizer use the constant directly and the taint never reaches the
//! primitive (seen at opt-level "s"). [`taint_ptr`] hands the fixture a
//! pointer laundered through `black_box`, which it must load through;
//! [`taint_scalar`] re-reads a by-value scalar from its tainted slot.

/// Taint `value` and return a pointer to it the optimizer cannot trace back
/// to the local, so the fixture loads the tainted bytes.
pub(crate) fn taint_ptr<T>(value: &T) -> *const T {
    krabi_caliper::host::ctgrind::taint_val(value);
    core::hint::black_box(value as *const T)
}

/// Taint a by-value secret and re-read it from the tainted slot.
pub(crate) fn taint_scalar<T: Copy>(value: T) -> T {
    let slot = value;
    krabi_caliper::host::ctgrind::taint_val(&slot);
    // SAFETY: `slot` is a live, initialised local.
    unsafe { core::ptr::read_volatile(&slot) }
}

/// Binary: `(T,N) × (T,N) → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_bin {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], b: *const [$T; $N], out: *mut [$T; $N]);
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            unsafe {
                $name(a, b, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Unary: `(T,N) → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_un {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], out: *mut [$T; $N]);
            }
            let a: [$T; $N] = [0; $N];
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            unsafe {
                $name(a, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Predicate: `(T,N) → u8`.
#[macro_export]
macro_rules! fbx_ctgrind_pred {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N]) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let r = unsafe { $name(a) };
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Binary predicate: `(T,N) × (T,N) → u8`.
#[macro_export]
macro_rules! fbx_ctgrind_pred2 {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], b: *const [$T; $N]) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            let r = unsafe { $name(a, b) };
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Bit-count: `(T,N) → u32`.
#[macro_export]
macro_rules! fbx_ctgrind_count {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N]) -> u32;
            }
            let a: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let r = unsafe { $name(a) };
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Shift: `(T,N) × scalar → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_shift {
    ($name:ident, $T:ty, $N:literal, $NT:ty) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], n: $NT, out: *mut [$T; $N]);
            }
            let a: [$T; $N] = [0; $N];
            let n: $NT = 0;
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let n = $crate::ctgrind_shapes::taint_scalar(n);
            unsafe {
                $name(a, n, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Checked binary: `(T,N) × (T,N) → (T,N) + u8`.
#[macro_export]
macro_rules! fbx_ctgrind_checked_bin {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], b: *const [$T; $N], out: *mut [$T; $N]) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            let r = unsafe { $name(a, b, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Checked unary with scalar: `(T,N) × scalar → (T,N) + u8`.
#[macro_export]
macro_rules! fbx_ctgrind_checked_scalar {
    ($name:ident, $T:ty, $N:literal, $ST:ty) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], s: $ST, out: *mut [$T; $N]) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let s: $ST = 0;
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let s = $crate::ctgrind_shapes::taint_scalar(s);
            let r = unsafe { $name(a, s, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Checked unary: `(T,N) → (T,N) + u8`.
#[macro_export]
macro_rules! fbx_ctgrind_checked_un {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], out: *mut [$T; $N]) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let r = unsafe { $name(a, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Conditional select: `(T,N) × (T,N) × u8 → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_cond_select {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(a: *const [$T; $N], b: *const [$T; $N], choice: u8, out: *mut [$T; $N]);
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let choice: u8 = 0;
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            let choice = $crate::ctgrind_shapes::taint_scalar(choice);
            unsafe {
                $name(a, b, choice, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Widening carrying mul: `(T,N) × (T,N) × (T,N) → (T,N) lo + (T,N) hi`.
/// A two-array-output shape unique to ct-fixtures — the kind that used to
/// require a harness release before the adapters moved local.
#[macro_export]
macro_rules! fbx_ctgrind_carrying_mul {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    carry: *const [$T; $N],
                    lo: *mut [$T; $N],
                    hi: *mut [$T; $N],
                );
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let carry: [$T; $N] = [0; $N];
            let mut lo: [$T; $N] = [0; $N];
            let mut hi: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            let carry = $crate::ctgrind_shapes::taint_ptr(&carry);
            unsafe {
                $name(a, b, carry, &mut lo, &mut hi);
            }
            krabi_caliper::host::ctgrind::untaint(&lo);
            krabi_caliper::host::ctgrind::untaint(&hi);
            let _ = ::core::hint::black_box(lo);
            let _ = ::core::hint::black_box(hi);
        });
    };
}

/// CIOS row op: `(mult:[T,N], acc:[T,N], scalar:T, carry:T) → acc'[T,N] + T`.
/// Two single-limb `T` scalar secrets alongside two arrays — another shape
/// unique to ct-fixtures, added locally.
#[macro_export]
macro_rules! fbx_ctgrind_mul_acc {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(
                    mult: *const [$T; $N],
                    acc: *const [$T; $N],
                    scalar: $T,
                    carry: $T,
                    out: *mut [$T; $N],
                ) -> $T;
            }
            let mult: [$T; $N] = [0; $N];
            let acc: [$T; $N] = [0; $N];
            let scalar: $T = 0;
            let carry: $T = 0;
            let mut out: [$T; $N] = [0; $N];
            let mult = $crate::ctgrind_shapes::taint_ptr(&mult);
            let acc = $crate::ctgrind_shapes::taint_ptr(&acc);
            let scalar = $crate::ctgrind_shapes::taint_scalar(scalar);
            let carry = $crate::ctgrind_shapes::taint_scalar(carry);
            let r = unsafe { $name(mult, acc, scalar, carry, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Carrying add: `(T,N) × (T,N) × bool → (T,N) + u8`.
#[macro_export]
macro_rules! fbx_ctgrind_carrying_add {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    carry: bool,
                    out: *mut [$T; $N],
                ) -> u8;
            }
            let a: [$T; $N] = [0; $N];
            let b: [$T; $N] = [0; $N];
            let carry: bool = false;
            let mut out: [$T; $N] = [0; $N];
            let a = $crate::ctgrind_shapes::taint_ptr(&a);
            let b = $crate::ctgrind_shapes::taint_ptr(&b);
            let carry = $crate::ctgrind_shapes::taint_scalar(carry);
            let r = unsafe { $name(a, b, carry, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Pointer-based secret shift amount → array. `(*const u32) → (T,N)`.
/// Direction-agnostic: the shape is identical for a secret-amount `<<` or
/// `>>` (public value baked into the fixture body, only the amount tainted).
#[macro_export]
macro_rules! fbx_ctgrind_asym_shift_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(amount: *const u32, out: *mut [$T; $N]);
            }
            let amount: u32 = 0;
            let mut out: [$T; $N] = [0; $N];
            let amount = $crate::ctgrind_shapes::taint_ptr(&amount);
            unsafe {
                $name(amount, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Pointer-based secret choice → array. `(*const u8) → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_asym_select_u8 {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(choice: *const u8, out: *mut [$T; $N]);
            }
            let choice: u8 = 0;
            let mut out: [$T; $N] = [0; $N];
            let choice = $crate::ctgrind_shapes::taint_ptr(&choice);
            unsafe {
                $name(choice, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
        });
    };
}

/// Pointer-based secret exponent → array + validity byte.
/// `(*const u32) → (T,N) + u8`.
#[macro_export]
macro_rules! fbx_ctgrind_asym_pow_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(exp: *const u32, out: *mut [$T; $N]) -> u8;
            }
            let exp: u32 = 0;
            let mut out: [$T; $N] = [0; $N];
            let exp = $crate::ctgrind_shapes::taint_ptr(&exp);
            let r = unsafe { $name(exp, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}
