//! Per-architecture forbidden / allowed mnemonic regex tables.
//!
//! These are raw regex strings, anchored at start/end of the mnemonic
//! field (the first whitespace-delimited token after the leading
//! address on each disassembly line). The parser splits on whitespace
//! and uses `regex::Regex::is_match` on the mnemonic alone.

// =============================================================================
// Thumb (Cortex-M0 / M3 / M4 / M7 / M33 / M55) — armv6m, armv7m, armv7em
// =============================================================================
//
// Conditional PC-relative branches: b.eq, b.ne, b.cs, b.hs, b.cc, b.lo,
//   b.mi, b.pl, b.vs, b.vc, b.hi, b.ls, b.ge, b.lt, b.gt, b.le
//   — plus the .n / .w width suffixes that llvm-objdump emits.
// Compare-and-branch: cbz, cbnz (armv7m+ only, not armv6m).
// Table branch: tbb, tbh (armv7m+ only).
//
// Allowed (CT-friendly): IT-block predicate execution. The parser tracks
// IT state separately and only flags conditional mnemonics that appear
// *outside* an active IT window.

pub const THUMB_FORBIDDEN: &[&str] = &[
    r"^b(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)(\.[nw])?$",
    r"^cbn?z$",
    r"^tb[bh]$",
];

pub const THUMB_ALLOWED: &[&str] = &[
    // IT block headers. Inside the IT window the parser allows the
    // following conditional mnemonics (handled in parse::it_state).
    r"^it[te]{0,3}$",
];

// =============================================================================
// RISC-V (riscv32imc, riscv32imac, riscv32imafc, etc.)
// =============================================================================
//
// RISC-V has no conditional move or predicate execution. Every branch
// changes PC. CT code must be xor/and/mask-based; any conditional
// branch in a Ct primitive is a violation.
//
// The gt/le/gtu/leu alternatives cover LLVM-printed pseudo-mnemonic
// aliases (bgt, ble, bgtu, bleu, bgtz, blez) — `llvm-objdump` prints
// these by default rather than the canonical bge/blt operand-swapped
// forms, so a Ct regression that lowered to one of them would
// otherwise slip past the gate.

pub const RISCV_FORBIDDEN: &[&str] = &[
    r"^b(eq|ne|lt|ge|gt|le|ltu|geu|gtu|leu)z?$",
    r"^c\.b(eqz|nez)$",
];

// =============================================================================
// AVR (atmega328p)
// =============================================================================
//
// AVR's conditional branches are br<cc>, and there are also "skip next
// instruction" mnemonics (sbic, sbis, sbrc, sbrs, cpse) — these aren't
// PC-relative jumps in the usual sense, but they ARE data-dependent
// control flow (the next instruction may or may not execute), so we
// flag them.

pub const AVR_FORBIDDEN: &[&str] = &[
    r"^br(cc|cs|eq|ge|hc|hs|id|ie|lo|lt|mi|ne|pl|sh|tc|ts|vc|vs)$",
    r"^s(bic|bis|brc|brs)$",
    r"^cpse$",
];

// =============================================================================
// AArch64 (Cortex-A, Apple Silicon, M-series datacenter, etc.)
// =============================================================================
//
// Forbidden: b.<cond>, cbz/cbnz, tbz/tbnz.
// Allowed: csel / csinc / csinv / csneg / cset / csetm / ccmp / ccmn —
// the conditional-select family is branch-free and is the CT idiom.

pub const AARCH64_FORBIDDEN: &[&str] = &[
    r"^b\.(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le|al|nv)$",
    r"^cbn?z$",
    r"^tbn?z$",
];

pub const AARCH64_ALLOWED: &[&str] = &[r"^cs(el|inc|inv|neg|et|etm)$", r"^ccmp[en]?$", r"^ccmn$"];

// =============================================================================
// x86_64
// =============================================================================
//
// Forbidden: the full j<cc> family.
// Allowed: cmov<cc> (conditional-move), set<cc> (flag→byte, branch-free),
// sbb (subtract-with-borrow, used in the borrow-as-mask idiom).

pub const X86_64_FORBIDDEN: &[&str] =
    &[r"^j(e|ne|z|nz|a|ae|b|be|c|nc|g|ge|l|le|o|no|s|ns|p|np|pe|po|cxz|ecxz|rcxz)$"];

pub const X86_64_ALLOWED: &[&str] = &[r"^cmov[a-z]+$", r"^set[a-z]+$", r"^sbb[bwlq]?$"];

// =============================================================================
// Call instructions (per arch)
// =============================================================================
//
// Used by the reachability walker: from each fixture symbol, scan its
// disassembly for any of these mnemonics and follow the call target to
// expand the inspection scope to reachable helpers. The walker doesn't
// flag these mnemonics — it just uses them as graph edges.

pub const THUMB_CALL: &[&str] = &[r"^blx?$"];
pub const AARCH64_CALL: &[&str] = &[r"^bl$", r"^blr$"];
pub const RISCV_CALL: &[&str] = &[r"^jal$", r"^jalr$", r"^c\.jal$", r"^c\.jalr$"];
pub const AVR_CALL: &[&str] = &[r"^r?call$", r"^icall$", r"^eicall$"];
pub const X86_64_CALL: &[&str] = &[r"^callq?$"];
