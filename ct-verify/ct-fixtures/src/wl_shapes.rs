//! `emit_wl_*` fixture adapters: turn a shared `ct_workload` op into an
//! `extern "C"` fixture (+ its ctgrind registration) per carrier × width.

/// `bin`-shape adapter: `(a, b) -> out`. Generates the `extern "C"` fixture
/// (and, under the `ctgrind` feature, its taint registration) for one
/// op × carrier × width by constructing the carrier through [`FixtureCarrier`],
/// calling the shared catalog op, and reading the result back. The op and its
/// input values are single-sourced; only the carrier + width vary here.
#[macro_export]
macro_rules! emit_wl_bin {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_bin!($sym, $T, $N, |aw, bw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            let b = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(bw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a, b))
        });
    };
}

/// `un` shape: `(a) -> out`.
#[macro_export]
macro_rules! emit_wl_un {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_un!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a))
        });
    };
}

/// `count` shape: `(a) -> u32`.
#[macro_export]
macro_rules! emit_wl_count {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_count!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            $op(a)
        });
    };
}

/// `pred` shape: `(a) -> u8`.
#[macro_export]
macro_rules! emit_wl_pred {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_pred!($sym, $T, $N, |aw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            $op(a)
        });
    };
}

/// `pred2` shape: `(a, b) -> u8`.
#[macro_export]
macro_rules! emit_wl_pred2 {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_pred2!($sym, $T, $N, |aw, bw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            let b = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(bw);
            $op(a, b)
        });
    };
}

/// `shift` shape: `(a, amount) -> out`. `$NT` is the amount type (`usize`/`u32`).
#[macro_export]
macro_rules! emit_wl_shift {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal, $NT:ty) => {
        $crate::ct_fix_shift!($sym, $T, $N, $NT, |aw, n| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&$op(a, n))
        });
    };
}

/// `checked_bin` shape: `(a, b) -> (out, u8)`. The op returns a `CtOption`;
/// this splits it into the value (zero fallback) and the validity byte.
#[macro_export]
macro_rules! emit_wl_checked_bin {
    ($sym:ident, $op:path, $carrier:ty, $T:ty, $N:literal) => {
        $crate::ct_fix_checked_bin!($sym, $T, $N, |aw, bw| {
            let a = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(aw);
            let b = <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words(bw);
            let res = $op(a, b);
            let valid = res.is_some().unwrap_u8();
            let value = res.unwrap_or(
                <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::from_words([0; $N]),
            );
            (
                <$carrier as $crate::catalog::FixtureCarrier<$T, $N>>::to_words(&value),
                valid,
            )
        });
    };
}
