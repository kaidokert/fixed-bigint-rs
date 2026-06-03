//! ctgrind fixture macros — one per ABI shape in ct-fixtures.
//!
//! Each macro emits:
//!   * an `extern "C"` declaration matching the fixture's ABI
//!   * a `run_<name>()` Rust wrapper that allocates buffers, taints the
//!     secret inputs with `MAKE_MEM_UNDEFINED`, calls the symbol, then
//!     marks the output buffer DEFINED so its post-call use (the
//!     `black_box`) doesn't itself trip Valgrind
//!   * an `inventory::submit!` registration into `Fixture`
//!
//! Mirrors the ABI shapes declared by ct-fixtures' `ct_fix_*` macros.

/// Binary fixture: (T,N) × (T,N) → (T,N).
#[macro_export]
macro_rules! ctgrind_bin {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    out: *mut [$T; $N],
                );
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let b: [$T; $N] = [0; $N];
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint(&b);
                unsafe { $name(&a, &b, &mut out); }
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

/// Unary fixture: (T,N) → (T,N).
#[macro_export]
macro_rules! ctgrind_un {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N], out: *mut [$T; $N]);
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                unsafe { $name(&a, &mut out); }
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

/// Predicate fixture: (T,N) → u8.
#[macro_export]
macro_rules! ctgrind_pred {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N]) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                let r = unsafe { $name(&a) };
                $crate::macros::untaint_val(&r);
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

/// Binary predicate fixture: (T,N) × (T,N) → u8.
#[macro_export]
macro_rules! ctgrind_pred2 {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N], b: *const [$T; $N]) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let b: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint(&b);
                let r = unsafe { $name(&a, &b) };
                $crate::macros::untaint_val(&r);
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

/// Bit-count fixture: (T,N) → u32.
#[macro_export]
macro_rules! ctgrind_count {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N]) -> u32;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                let r = unsafe { $name(&a) };
                $crate::macros::untaint_val(&r);
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

/// Shift fixture: (T,N) × scalar → (T,N).
#[macro_export]
macro_rules! ctgrind_shift {
    ($name:ident, $T:ty, $N:literal, $NT:ty) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N], n: $NT, out: *mut [$T; $N]);
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                // `black_box(0)` opacifies the literal — without it, release-
                // LTO constant-propagates the 0 past `taint_val(&n)` (which
                // only sets Valgrind metadata, not memory contents) and the
                // taint never reaches the called primitive.
                let n: $NT = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint_val(&n);
                unsafe { $name(&a, n, &mut out); }
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

/// Checked-binary fixture: (T,N) × (T,N) → (T,N) + u8.
#[macro_export]
macro_rules! ctgrind_checked_bin {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    out: *mut [$T; $N],
                ) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let b: [$T; $N] = [0; $N];
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint(&b);
                let r = unsafe { $name(&a, &b, &mut out) };
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

/// Checked-unary-with-scalar fixture: (T,N) × scalar → (T,N) + u8.
#[macro_export]
macro_rules! ctgrind_checked_scalar {
    ($name:ident, $T:ty, $N:literal, $ST:ty) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N], s: $ST, out: *mut [$T; $N]) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                // See `ctgrind_shift` for the `black_box(0)` rationale.
                let s: $ST = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint_val(&s);
                let r = unsafe { $name(&a, s, &mut out) };
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

/// Checked-unary fixture: (T,N) → (T,N) + u8.
#[macro_export]
macro_rules! ctgrind_checked_un {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(a: *const [$T; $N], out: *mut [$T; $N]) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                let r = unsafe { $name(&a, &mut out) };
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

/// `cond_select` fixture: (T,N) × (T,N) × u8 → (T,N).
#[macro_export]
macro_rules! ctgrind_cond_select {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    choice: u8,
                    out: *mut [$T; $N],
                );
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let b: [$T; $N] = [0; $N];
                // See `ctgrind_shift` for the `black_box(0)` rationale.
                let choice: u8 = ::core::hint::black_box(0);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint(&b);
                $crate::macros::taint_val(&choice);
                unsafe { $name(&a, &b, choice, &mut out); }
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

/// `carrying_add` fixture: (T,N) × (T,N) × bool → (T,N) + u8.
#[macro_export]
macro_rules! ctgrind_carrying_add {
    ($name:ident, $T:ty, $N:literal) => {
        paste::paste! {
            extern "C" {
                fn $name(
                    a: *const [$T; $N],
                    b: *const [$T; $N],
                    carry: bool,
                    out: *mut [$T; $N],
                ) -> u8;
            }
            #[allow(non_snake_case)]
            fn [<run_ $name>]() {
                let a: [$T; $N] = [0; $N];
                let b: [$T; $N] = [0; $N];
                // See `ctgrind_shift` for the `black_box(false)` rationale.
                let carry: bool = ::core::hint::black_box(false);
                let mut out: [$T; $N] = [0; $N];
                $crate::macros::taint(&a);
                $crate::macros::taint(&b);
                $crate::macros::taint_val(&carry);
                let r = unsafe { $name(&a, &b, carry, &mut out) };
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

// ============================================================================
// Taint helpers — thin wrappers around crabgrind's memcheck client requests.
// ============================================================================

pub fn taint<T>(buf: &[T]) {
    crate::valgrind::mark_undefined(buf.as_ptr() as *const u8, ::core::mem::size_of_val(buf));
}

pub fn taint_val<T>(v: &T) {
    crate::valgrind::mark_undefined(v as *const T as *const u8, ::core::mem::size_of::<T>());
}

pub fn untaint<T>(buf: &[T]) {
    crate::valgrind::mark_defined(buf.as_ptr() as *const u8, ::core::mem::size_of_val(buf));
}

pub fn untaint_val<T>(v: &T) {
    crate::valgrind::mark_defined(v as *const T as *const u8, ::core::mem::size_of::<T>());
}
