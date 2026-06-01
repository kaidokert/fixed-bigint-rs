//! Per-target specifications: triple, toolchain pin, and the mnemonic
//! tables used by the parser.

use crate::mnemonics;

#[allow(dead_code)]
// `priority` and `toolchain` are documentation-only fields used by
// `--list-targets`.
#[derive(Debug, Clone, Copy)]
pub struct TargetSpec {
    pub triple: &'static str,
    pub priority: u8,
    /// "stable" | "1.85" | "nightly-YYYY-MM-DD". The driver doesn't
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
        toolchain: "1.85",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: true,
        extra_cargo_args: &[],
    },
    TargetSpec {
        triple: "thumbv7m-none-eabi",
        priority: 1,
        toolchain: "1.85",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: true,
        extra_cargo_args: &[],
    },
    // Priority 2: Cortex-M0
    TargetSpec {
        triple: "thumbv6m-none-eabi",
        priority: 2,
        toolchain: "1.85",
        forbidden: mnemonics::THUMB_FORBIDDEN,
        allowed_cmov: mnemonics::THUMB_ALLOWED,
        thumb_it_blocks: false, // armv6m has no IT; no allowlist needed
        extra_cargo_args: &[],
    },
    // Priority 3: 32-bit RISC-V
    TargetSpec {
        triple: "riscv32imc-unknown-none-elf",
        priority: 3,
        toolchain: "1.85",
        forbidden: mnemonics::RISCV_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        extra_cargo_args: &[],
    },
    TargetSpec {
        triple: "riscv32imac-unknown-none-elf",
        priority: 3,
        toolchain: "1.85",
        forbidden: mnemonics::RISCV_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        extra_cargo_args: &[],
    },
    // Priority 4: 8-bit AVR (nightly-only, needs build-std + target-cpu).
    // Modern rustc uses the `avr-none` triple and requires an explicit
    // `-C target-cpu=<mcu>`. The CI workflow sets RUSTFLAGS accordingly
    // and passes -Z build-std=core via extra_cargo_args.
    TargetSpec {
        triple: "avr-none",
        priority: 4,
        toolchain: "nightly-2026-05-30",
        forbidden: mnemonics::AVR_FORBIDDEN,
        allowed_cmov: &[],
        thumb_it_blocks: false,
        extra_cargo_args: &["-Z", "build-std=core"],
    },
    // Priority 5: aarch64
    TargetSpec {
        triple: "aarch64-unknown-linux-gnu",
        priority: 5,
        toolchain: "1.85",
        forbidden: mnemonics::AARCH64_FORBIDDEN,
        allowed_cmov: mnemonics::AARCH64_ALLOWED,
        thumb_it_blocks: false,
        extra_cargo_args: &[],
    },
    // Priority 6: x86_64
    TargetSpec {
        triple: "x86_64-unknown-linux-gnu",
        priority: 6,
        toolchain: "1.85",
        forbidden: mnemonics::X86_64_FORBIDDEN,
        allowed_cmov: mnemonics::X86_64_ALLOWED,
        thumb_it_blocks: false,
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
        extra_cargo_args: &[],
    },
];

pub fn lookup(triple: &str) -> Option<&'static TargetSpec> {
    TARGETS.iter().find(|t| t.triple == triple)
}
