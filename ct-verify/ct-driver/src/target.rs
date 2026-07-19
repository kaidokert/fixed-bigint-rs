//! Per-target specifications: triple, toolchain pin, and the mnemonic
//! tables used by the parser.

use krabi_caliper::host::isa as mnemonics;

#[allow(dead_code)]
// `priority` and `toolchain` are documentation-only fields used by
// `--list-targets`.
#[derive(Debug, Clone, Copy)]
pub struct TargetSpec {
    pub triple: &'static str,
    pub priority: u8,
    /// "stable" | "1.86" | "nightly-YYYY-MM-DD". The driver doesn't
    /// switch toolchains itself — CI sets up the right one and the
    /// triple drives `cargo build --target=<triple>`. The pin is here
    /// for documentation and so the driver can warn if the active
    /// toolchain doesn't match.
    pub toolchain: &'static str,
    /// Regexes that, when they match the mnemonic at any insn line of
    /// any fixture's body, count as a violation.
    pub forbidden: &'static [&'static str],
    /// Regexes that, when matched, are explicitly OK even though they
    /// look conditional. E.g., aarch64 `csel` / x64 `cmovcc` / thumb
    /// `IT` predicate execution.
    pub allowed_cmov: &'static [&'static str],
    /// Engage the thumb IT-state machine.
    pub thumb_it_blocks: bool,
    /// Call-instruction mnemonics for this arch (regex). Used by the
    /// reachability walker to follow edges from fixtures into helpers;
    /// these aren't flagged as violations themselves.
    pub call_mnemonics: &'static [&'static str],
    /// Helper symbol patterns whose forbidden mnemonics should be
    /// suppressed — typically because the body is a public-parameter
    /// loop (`for i in 0..N` where `N` is a compile-time constant),
    /// which compiles to a branchful but CT-safe `cmp/b.lt`. Static
    /// pattern matching can't distinguish those from secret-dependent
    /// branches, so this list is a small per-target escape hatch.
    pub allowed_helpers: &'static [&'static str],
    /// Per-target extras layered on top of `allowed_helpers`. Reserved
    /// for branches whose root cause is architecture-specific (e.g.,
    /// armv6m lacks the `clz` instruction, so `u32::leading_zeros()`
    /// lowers to a branchful software polynomial in `core` itself).
    /// These don't belong in the shared list because every other arch
    /// should keep grepping for them.
    pub extra_allowed_helpers: &'static [&'static str],
    /// Extra cargo args needed for this target (e.g., `-Z build-std=core`
    /// for AVR).
    pub extra_cargo_args: &'static [&'static str],
}

/// All targets we know how to verify, in priority order.
pub const TARGETS: &[TargetSpec] = &[
    // Priority 1: Cortex-M3/M4
    TargetSpec {
        triple: "thumbv7em-none-eabi",
        priority: 1,
        toolchain: "1.86",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: true,
        call_mnemonics: mnemonics::THUMB_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    TargetSpec {
        triple: "thumbv7m-none-eabi",
        priority: 1,
        toolchain: "1.86",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: true,
        call_mnemonics: mnemonics::THUMB_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    // Priority 2: Cortex-M0
    TargetSpec {
        triple: "thumbv6m-none-eabi",
        priority: 2,
        toolchain: "1.86",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: false, // armv6m has no IT; no allowlist needed
        call_mnemonics: mnemonics::THUMB_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: THUMBV6M_EXTRA_HELPERS,
        extra_cargo_args: &[],
    },
    // Priority 3: 32-bit RISC-V
    TargetSpec {
        triple: "riscv32imc-unknown-none-elf",
        priority: 3,
        toolchain: "1.86",
        forbidden: mnemonics::RISCV_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::RISCV_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    TargetSpec {
        triple: "riscv32imac-unknown-none-elf",
        priority: 3,
        toolchain: "1.86",
        forbidden: mnemonics::RISCV_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::RISCV_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    // Priority 4: 8-bit AVR (nightly-only, needs build-std + target-cpu).
    // Modern rustc uses the `avr-none` triple and requires an explicit
    // `-C target-cpu=<mcu>`. The CI workflow sets RUSTFLAGS accordingly
    // and passes -Z build-std=core via extra_cargo_args.
    TargetSpec {
        triple: "avr-none",
        priority: 4,
        toolchain: "nightly",
        forbidden: mnemonics::AVR_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::AVR_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &["-Z", "build-std=core"],
    },
    // Priority 5: aarch64
    TargetSpec {
        triple: "aarch64-unknown-linux-gnu",
        priority: 5,
        toolchain: "1.86",
        forbidden: mnemonics::AARCH64_FORBIDDEN,
        allowed_cmov: mnemonics::AARCH64_ALLOWED,
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::AARCH64_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    // Priority 6: x86_64
    TargetSpec {
        triple: "x86_64-unknown-linux-gnu",
        priority: 6,
        toolchain: "1.86",
        forbidden: mnemonics::X86_64_FORBIDDEN,
        allowed_cmov: mnemonics::X86_64_ALLOWED,
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::X86_64_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
    // Host fallback: aarch64-apple-darwin. Same mnemonic tables as
    // aarch64-linux. The CI matrix doesn't run this; it's here so
    // `cargo run -p ct-driver` works on macOS dev boxes without --target.
    TargetSpec {
        triple: "aarch64-apple-darwin",
        priority: 99,
        toolchain: "stable",
        forbidden: mnemonics::AARCH64_FORBIDDEN,
        allowed_cmov: mnemonics::AARCH64_ALLOWED,
        thumb_it_blocks: false,
        call_mnemonics: mnemonics::AARCH64_CALL,
        allowed_helpers: HELPER_ALLOWLIST,
        extra_allowed_helpers: &[],
        extra_cargo_args: &[],
    },
];

/// Per-helper allowlist shared across every backend.
///
/// Sharing is intentional: each entry's CT-safety reasoning is
/// **source-semantic** — the function body is a public-bounded loop
/// (`for i in 0..N` with compile-time `N`, `while k < usize::BITS`,
/// or a copy/zero of a compile-time-sized buffer) — not a property of
/// any particular backend's lowering. A public-bounded loop compiles
/// to a branchful `cmp/b.lt` on every architecture we target; the
/// classification holds because the bound itself is public, not
/// because aarch64 happens to lower it a certain way.
///
/// Empirical check on this PR: each target in the CI matrix
/// (thumbv6m/7m/7em, riscv32imc/imac, aarch64-linux, x86_64-linux,
/// avr-none) was run through the helper-scope walker. Targets pass
/// with zero residual helper violations once their target-specific
/// upstream concerns are partitioned into `extra_allowed_helpers`
/// (e.g., thumbv6m's missing CLZ pulls in `__clzsi2` etc.). Anything
/// truly backend-specific belongs there, not here.
///
/// Keep entries narrow — match on demangled-ish substrings of the
/// rust symbol mangling so a typo or rename surfaces as a hard scope
/// miss rather than a silent skip. Add an entry only after confirming
/// the helper's body is a public-bounded loop; document the reason
/// inline. The same property is exercised independently by the
/// ctgrind harness on its supported targets, which catches secret
/// dependence directly through taint.
const HELPER_ALLOWLIST: &[&str] = &[
    // Bit-shift helpers. const_shl_ct / shr_ct iterate usize::BITS times
    // with a per-iteration mask-AND-XOR select; const_shl_impl / shr_impl
    // are reached from them with a non-tainted `amount = 1 << k`.
    r"fixed_bigint9fixeduint12const_shl_ct",
    r"fixed_bigint9fixeduint12const_shr_ct",
    r"fixed_bigint9fixeduint14const_shl_impl",
    r"fixed_bigint9fixeduint14const_shr_impl",
    // Shift-amount normaliser. Reached from Nct paths only after PR #121
    // moved the Ct arm off it; the branches are on `bits >= bit_size`
    // (Nct caller's concern).
    r"fixed_bigint9fixeduint12bit_ops_impl22normalize_shift_amount",
    // Per-limb CT select. Branches are loop counter < N (compile-time).
    r"fixed_bigint9fixeduint15const_ct_select",
    // Per-limb scanners — leading/trailing zero counts, is_zero / is_one.
    // Loop bound is N (compile-time constant).
    r"fixed_bigint9fixeduint16const_is_zero_ct",
    r"fixed_bigint9fixeduint15const_is_one_ct",
    r"fixed_bigint9fixeduint22const_leading_zeros_ct",
    r"fixed_bigint9fixeduint23const_trailing_zeros_ct",
    // Per-limb arithmetic — N-bounded loops.
    r"fixed_bigint9fixeduint14add_with_carry",
    r"fixed_bigint9fixeduint15sub_with_borrow",
    r"fixed_bigint9fixeduint9const_mul",
    r"fixed_bigint9fixeduint8add_impl",
    r"fixed_bigint9fixeduint8sub_impl",
    // ct_checked_pow's square-and-multiply ladder iterates u32::BITS
    // times.
    r"fixed_bigint9fixeduint.*ct_checked_pow",
    // Trait impls on FixedUInt: bitwise ops, prim-int family, num_traits
    // identity, subtle's ConditionallySelectable / ConstantTime*. All
    // per-limb N-bounded loops.
    r"core\.\.ops\.\.bit\.\.(?:Not|BitOr|BitAnd|BitXor).*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    // const-num-traits trait impls on FixedUInt. The v0.4 migration
    // moved these to the external `const-num-traits` crate (path:
    // `const_num_traits::{int,identities,bounds,sign}::TraitName`).
    // The body shape is unchanged: all-N-bounded limb loops.
    r"const_num_traits\.\.int\.\.PrimBits.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    r"const_num_traits\.\.identities\.\.(?:Const)?(?:Zero|One).*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    r"const_num_traits\.\.bounds\.\.Bounded.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    r"const_num_traits\.\.sign\.\.Unsigned.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    // const-num-traits' Ct* trait wrappers (`ops::ct::Ct{IsZero,Parity,
    // IsPowerOfTwo,CheckedAdd,CheckedSub,CheckedMul}`) impl'd on
    // FixedUInt. The body is an N-bounded limb loop (AND-fold of
    // `ct_eq` against ZERO, or delegation to existing branchless
    // ops). Same shape as the predicate / arithmetic impls already
    // allowlisted.
    r"const_num_traits\.\.ops\.\.ct\.\.Ct(?:IsZero|Parity|IsPowerOfTwo|CheckedAdd|CheckedSub|CheckedMul)\b.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    // CtNonZero lives at `const_num_traits::typestate::CtNonZero`
    // (not in `ops::ct`); body is `ct_is_zero() + new_unchecked` so
    // covered by the CtIsZero allowance above, but spell it out so
    // a future move of the impl block isn't a silent regression.
    r"const_num_traits\.\.(?:ops\.\.typestate|typestate)\.\.CtNonZero.*fixed_bigint\.\.fixeduint",
    // Pre-migration mangled paths (kept for any vestigial codegen path
    // we haven't proven gone — comment out if a regex audit confirms
    // they're now dead).
    r"fixed_bigint\.\.const_numtraits\.\.ConstBitPrimInt.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    r"fixed_bigint\.\.const_numtraits\.\.ConstZero.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    r"fixed_bigint\.\.const_numtraits\.\.ConstBounded.*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    // FixedUInt's own from-byte-slice helpers (called from `From<[T; N]>`
    // through the byte-conversion path). Loop bound is `byte_index <
    // min(bytes.len(), N * WORD_SIZE)` — bytes.len() is the public
    // slice length, same shape as the per-limb helpers.
    r"fixed_bigint9fixeduint24impl_from_(?:le|be)_bytes_slice",
    // ARM EABI runtime helpers for 64-bit shifts (`__aeabi_ll{sl,sr}`).
    // Reached transitively from u64-backed `FixedUInt` shift/multiply
    // paths. Branchful on the shift amount, which we always pass as a
    // public counter (`1 << k` from a fixed iteration). Same shape as
    // the `__ashl{di,ti}3` family already allowlisted below.
    r"^_?__aeabi_l(?:lsl|lsr|asr)$",
    // Subtle impls use `<Self as Trait>` mangling (Self first, then
    // `as`, then trait) rather than the `<impl Trait for Self>`
    // mangling the bitwise / num_traits impls above use.
    r"fixed_bigint\.\.fixeduint\.\.FixedUInt.*subtle\.\.ConditionallySelectable",
    r"fixed_bigint\.\.fixeduint\.\.FixedUInt.*subtle\.\.ConstantTimeEq",
    r"fixed_bigint\.\.fixeduint\.\.FixedUInt.*subtle\.\.ConstantTimeGreater",
    // subtle's primitive u32 ct_gt: loop bound is u32::BITS = 32.
    r"\$LT\$u32\$u20\$as\$u20\$subtle\.\.ConstantTimeGreater\$GT\$5ct_gt",
    // subtle's slice `<[T] as ConstantTimeEq>::ct_eq`: iterates the
    // slice element-by-element, length is the slice length (public).
    // Same shape as our per-limb N-bounded loops.
    r"\$LT\$\$u5b\$T\$u5d\$.*subtle\.\.ConstantTimeEq.*5ct_eq",
    // Compiler-builtin and libc-class byte-copy / byte-zero helpers
    // reached transitively from array initialisation. All branchful
    // on size (public parameter), not on data — same shape as our own
    // per-limb loops.
    //
    // ARM EABI variants on thumb targets:
    r"^_?__aeabi_(?:memcpy|memset|memclr|memmove)\d*$",
    // Bare libc-style names (Linux/Mach-O) and their `__` variants
    // emitted by compiler-builtins:
    r"^_?_?(?:mem(?:cpy|set|clr|move|cmp)|bcmp)$",
    // The Rust `compiler_builtins::mem::{memcpy,memset,memmove,memcmp}`
    // implementations (mangled `_ZN17compiler_builtins3mem…E`). On
    // bare-metal targets without a libc, the bare-name symbols above
    // resolve to these. Branchful on length only.
    r"compiler_builtins3mem(?:6memcpy|6memset|7memmove|6memcmp)",
    // compiler-rt 128-bit shift helpers (`__ashlti3`, `__ashrti3`,
    // `__lshrti3`) and their 64-bit twins on 32-bit targets
    // (`__ashldi3`, etc.). Reached from any FixedUInt shift whose
    // backing limb pair spans a register width. The internal branches
    // are on the shift count, which our Ct shift helpers always pass
    // as a public-bounded `1 << k` from a public iteration counter.
    r"^__(?:ashl|ashr|lshr)[dt]i3$",
];

/// Thumbv6m-specific extras layered onto `HELPER_ALLOWLIST`.
///
/// Cortex-M0 (armv6m) is the only target in our matrix without a CLZ
/// instruction, so std's `u{8,16,32,64}::leading_zeros` /
/// `trailing_zeros` intrinsics lower to a branchful software
/// polynomial inside `core` itself. Any function that inlines one of
/// them inherits those branches — and on armv6m without IT-block
/// predication, conditional sub-with-borrow on primitives and subtle's
/// own primitive `ct_eq` also expand to short `b<cc>` sequences rather
/// than the conditional moves used on armv7m+/aarch64/x86_64.
///
/// These are upstream concerns the asm-grep gate can't fix here. The
/// taint-based ctgrind harness still catches them on its supported
/// targets. Removing entries from this list is a tracked follow-up:
/// once `fixed-bigint` ships branchless replacements for the affected
/// intrinsics, the corresponding row drops out.
const THUMBV6M_EXTRA_HELPERS: &[&str] = &[
    // `<u8/u16/u32/u64 as ConstBitPrimInt>::leading_zeros` /
    // `trailing_zeros`: forward to `core`'s intrinsic. Branchful on
    // armv6m (no CLZ). v0.4 path:
    // `const_num_traits::int::PrimBits`.
    r"\$LT\$u(?:8|16|32|64)\$.*const_num_traits\.\.int\.\.PrimBits.*(?:leading|trailing)_zeros",
    r"\$LT\$u(?:8|16|32|64)\$.*fixed_bigint\.\.const_numtraits\.\.ConstBitPrimInt.*(?:leading|trailing)_zeros",
    // `<u8/u16/u32/u64 as BorrowingSub>::borrowing_sub`: the
    // `||` over two overflow flags compiles to a short conditional
    // branch on armv6m. CT-safe everywhere with IT or cmov.
    r"\$LT\$u(?:8|16|32|64)\$.*const_num_traits\.\.ops\.\.carrying\.\.BorrowingSub.*13borrowing_sub",
    r"\$LT\$u(?:8|16|32|64)\$.*fixed_bigint\.\.const_numtraits\.\.ConstBorrowingSub.*13borrowing_sub",
    // `OverflowingShl` / `OverflowingShr` for FixedUInt: the per-limb
    // shift body uses `<core::ops::Shl<usize>>` via a generic helper
    // whose innermost operation on armv6m is a primitive
    // `leading_zeros` inline (same root cause as the others above).
    r"const_num_traits\.\.ops\.\.overflowing\.\.OverflowingSh(?:l|r).*fixed_bigint\.\.fixeduint\.\.FixedUInt",
    // subtle's primitive `<u{8,16,32,64} as ConstantTimeEq>::ct_eq` —
    // upstream impl, branchful on armv6m for the same IT/cmov reason.
    r"\$LT\$u(?:8|16|32|64)\$.*subtle\.\.ConstantTimeEq.*5ct_eq",
    // ConstPowerOfTwo for FixedUInt: `next_power_of_two` and
    // `ct_checked_next_power_of_two` inline the primitive
    // `leading_zeros` above and inherit its branches on armv6m.
    r"fixed_bigint9fixeduint17power_of_two_impl.*next_power_of_two",
    r"fixed_bigint9fixeduint.*FixedUInt.*ct_checked_next_power_of_two",
    // compiler_builtins' software division — pulled in transitively
    // by the armv6m `leading_zeros` polynomial. Branchful on size.
    r"compiler_builtins3int.*specialized_div_rem",
    // compiler-rt runtime helpers only emitted on armv6m because the
    // ISA lacks the underlying instruction:
    //   __clzsi2 / __clzdi2  — software CLZ (no `clz` on armv6m)
    //   __udivmodsi4         — software u32 division (no `udiv`)
    //   __aeabi_llsl / llsr  — i64 shifts (no native 64-bit shifts)
    // Each is branchful on its count or magnitude operand, which is a
    // public parameter at every callsite we reach them through.
    r"^__clz[sd]i2$",
    r"^__udivmodsi4$",
    r"^__aeabi_l?ls[lr]$",
];

pub fn lookup(triple: &str) -> Option<&'static TargetSpec> {
    TARGETS.iter().find(|t| t.triple == triple)
}
