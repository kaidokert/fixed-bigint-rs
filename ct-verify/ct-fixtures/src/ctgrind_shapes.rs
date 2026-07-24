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
//! `black_box(0)` on the scalar secrets is required: without it release-LTO
//! constant-propagates the literal past `taint_val` (which sets Valgrind
//! metadata, not memory) and the taint never reaches the primitive.

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
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint(&b);
            unsafe {
                $name(&a, &b, &mut out);
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
            krabi_caliper::host::ctgrind::taint(&a);
            unsafe {
                $name(&a, &mut out);
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
            krabi_caliper::host::ctgrind::taint(&a);
            let r = unsafe { $name(&a) };
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
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint(&b);
            let r = unsafe { $name(&a, &b) };
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
            krabi_caliper::host::ctgrind::taint(&a);
            let r = unsafe { $name(&a) };
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
            let n: $NT = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint_val(&n);
            unsafe {
                $name(&a, n, &mut out);
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
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint(&b);
            let r = unsafe { $name(&a, &b, &mut out) };
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
            let s: $ST = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint_val(&s);
            let r = unsafe { $name(&a, s, &mut out) };
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
            krabi_caliper::host::ctgrind::taint(&a);
            let r = unsafe { $name(&a, &mut out) };
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
            let choice: u8 = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint(&b);
            krabi_caliper::host::ctgrind::taint_val(&choice);
            unsafe {
                $name(&a, &b, choice, &mut out);
            }
            krabi_caliper::host::ctgrind::untaint(&out);
            let _ = ::core::hint::black_box(out);
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
            let carry: bool = ::core::hint::black_box(false);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint(&a);
            krabi_caliper::host::ctgrind::taint(&b);
            krabi_caliper::host::ctgrind::taint_val(&carry);
            let r = unsafe { $name(&a, &b, carry, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}

/// Pointer-based secret shift amount → array. `(*const u32) → (T,N)`.
#[macro_export]
macro_rules! fbx_ctgrind_asym_shl_u32 {
    ($name:ident, $T:ty, $N:literal) => {
        krabi_caliper::ctgrind_fixture!($name, {
            unsafe extern "C" {
                fn $name(amount: *const u32, out: *mut [$T; $N]);
            }
            let amount: u32 = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint_val(&amount);
            unsafe {
                $name(&amount, &mut out);
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
            let choice: u8 = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint_val(&choice);
            unsafe {
                $name(&choice, &mut out);
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
            let exp: u32 = ::core::hint::black_box(0);
            let mut out: [$T; $N] = [0; $N];
            krabi_caliper::host::ctgrind::taint_val(&exp);
            let r = unsafe { $name(&exp, &mut out) };
            krabi_caliper::host::ctgrind::untaint(&out);
            krabi_caliper::host::ctgrind::untaint_val(&r);
            let _ = ::core::hint::black_box(out);
            let _ = ::core::hint::black_box(r);
        });
    };
}
