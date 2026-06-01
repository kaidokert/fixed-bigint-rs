//! Disassembly parser.
//!
//! Takes the textual output of `llvm-objdump --disassemble
//! --no-show-raw-insn --no-leading-addr` and splits it into per-symbol
//! function blocks. Then for each block runs the per-target mnemonic
//! check + the thumb IT-state machine + the unconditional-branch
//! direction classifier.

use std::collections::VecDeque;
use std::sync::LazyLock;

use regex::Regex;

use crate::target::TargetSpec;

// Symbol header regex: `<symbol_name>:`. llvm-objdump emits two shapes,
//   `0000000000000020 <_symbol_name>:`        (without --no-leading-addr)
//   `<_symbol_name>:`                         (with --no-leading-addr)
// — both end with `<sym>:`.
static HEADER_RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"<([^>]+)>:\s*$").unwrap());

// Instruction line: leading whitespace, then optional `address:`, then the
// mnemonic, then operands. With --no-leading-addr the address is still
// emitted (relative). Be permissive: strip the leading `address:` if
// present, take the first whitespace-delimited token as the mnemonic.
static INSN_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"^\s*(?:([0-9a-fA-F]+):)?\s+(\S+)(?:\s+(.*))?$").unwrap());

/// One disassembled function block.
#[derive(Debug)]
pub struct FunctionBlock {
    pub symbol: String,
    /// Each line: (offset_hex_string, mnemonic, full_line_text).
    pub insns: Vec<Insn>,
}

#[derive(Debug, Clone)]
pub struct Insn {
    pub offset: u64,
    pub mnemonic: String,
    pub full_line: String,
}

/// Parse the entire objdump output into function blocks.
pub fn split_blocks(objdump_out: &str) -> Vec<FunctionBlock> {
    let mut blocks: Vec<FunctionBlock> = Vec::new();
    let mut current: Option<FunctionBlock> = None;
    let mut implicit_offset: u64 = 0;

    for line in objdump_out.lines() {
        // Skip dividers and headers from the archive listing.
        if line.is_empty()
            || line.starts_with("Disassembly")
            || line.starts_with(';')
            || line.contains(":\tfile format ")
        {
            continue;
        }

        if let Some(caps) = HEADER_RE.captures(line) {
            // Flush previous block.
            if let Some(b) = current.take() {
                blocks.push(b);
            }
            let sym = caps.get(1).unwrap().as_str().to_string();
            current = Some(FunctionBlock {
                symbol: sym,
                insns: Vec::new(),
            });
            implicit_offset = 0;
            continue;
        }

        let Some(block) = current.as_mut() else {
            continue;
        };

        if let Some(caps) = INSN_RE.captures(line) {
            let offset = if let Some(parsed) = caps
                .get(1)
                .and_then(|m| u64::from_str_radix(m.as_str(), 16).ok())
            {
                // Keep implicit_offset in sync so a subsequent
                // address-less line continues from the right place.
                implicit_offset = parsed + 4;
                parsed
            } else {
                let o = implicit_offset;
                implicit_offset += 4; // arbitrary default; only used when address column is missing
                o
            };
            let mnemonic = caps
                .get(2)
                .map(|m| m.as_str().to_ascii_lowercase())
                .unwrap_or_default();
            // Skip lines that aren't actually instructions (e.g.,
            // `...` continuation lines from llvm-objdump).
            if mnemonic.is_empty() || mnemonic == "..." {
                continue;
            }
            block.insns.push(Insn {
                offset,
                mnemonic,
                full_line: line.trim_end().to_string(),
            });
        }
    }

    if let Some(b) = current.take() {
        blocks.push(b);
    }
    blocks
}

/// One detected branch violation.
#[allow(dead_code)] // `mnemonic` is used by `report.rs::ViolationOut` via `From`.
#[derive(Debug, Clone)]
pub struct Violation {
    pub symbol: String,
    pub offset: u64,
    pub mnemonic: String,
    pub line: String,
    /// The previous 2 instructions + the violating one, for review.
    pub context: Vec<String>,
}

/// Compiled regex set for a target.
pub struct Patterns {
    pub forbidden: Vec<Regex>,
    pub allowed: Vec<Regex>,
}

impl Patterns {
    pub fn build(spec: &TargetSpec) -> Self {
        Self {
            forbidden: spec
                .forbidden
                .iter()
                .map(|p| Regex::new(p).expect("bad forbidden regex"))
                .collect(),
            allowed: spec
                .allowed_cmov
                .iter()
                .map(|p| Regex::new(p).expect("bad allowed regex"))
                .collect(),
        }
    }

    pub fn forbidden_matches(&self, mnemonic: &str) -> bool {
        self.forbidden.iter().any(|r| r.is_match(mnemonic))
    }

    pub fn allowed_matches(&self, mnemonic: &str) -> bool {
        self.allowed.iter().any(|r| r.is_match(mnemonic))
    }
}

/// Scan one block for violations, applying the per-target rules.
pub fn scan_block(block: &FunctionBlock, spec: &TargetSpec, pat: &Patterns) -> Vec<Violation> {
    let mut violations = Vec::new();
    let mut recent: VecDeque<String> = VecDeque::with_capacity(3);

    // IT-state machine for thumb. `it_remaining > 0` means the next
    // `it_remaining` insns are predicated. A forbidden conditional
    // inside an active IT window is allowed.
    let mut it_remaining: u32 = 0;

    for insn in &block.insns {
        recent.push_back(insn.full_line.clone());
        if recent.len() > 3 {
            recent.pop_front();
        }

        let m = insn.mnemonic.as_str();

        // Thumb IT-block tracking. `it`, `itt`, `ite`, `ittt`, `itte`,
        // etc. — the trailing t/e letters describe whether the next
        // 1..4 instructions execute on true or false. We just need the
        // count.
        if spec.thumb_it_blocks && m.starts_with("it") && m.len() <= 5 {
            // it = 1 conditional, itt = 2, ittt = 3, itttt = 4.
            let n = m.len().saturating_sub(1) as u32; // "it" → 1, "itt" → 2, ...
            it_remaining = n;
            continue;
        }

        if pat.allowed_matches(m) {
            // Explicit allowlist hit (csel/cmov/IT etc.) — not a violation.
            if it_remaining > 0 {
                it_remaining -= 1;
            }
            continue;
        }

        if pat.forbidden_matches(m) {
            // Forbidden mnemonic. If it's inside an active IT window,
            // it's actually allowed (predicate execution, branch-free).
            if it_remaining > 0 {
                it_remaining -= 1;
                continue;
            }

            // Unconditional `b` is also caught by forbidden patterns if
            // any author adds it there; the default tables don't list
            // it as forbidden, so we don't special-case it here. The
            // user-controlled regex set is sovereign.

            violations.push(Violation {
                symbol: block.symbol.clone(),
                offset: insn.offset,
                mnemonic: insn.mnemonic.clone(),
                line: insn.full_line.clone(),
                context: recent.iter().cloned().collect(),
            });
            continue;
        }

        // Non-conditional instruction (mov, add, ldr, bl, ...). If we
        // were in an IT window, count it down.
        if it_remaining > 0 {
            it_remaining -= 1;
        }
    }

    violations
}

/// Decide which symbols the driver inspects.
///
/// **v1 scope**: only the fixture wrappers themselves
/// (`ct_fix__*` and `nct_fix__*`). Helper symbols compiled into the
/// staticlib are NOT inspected here, for two reasons:
///
/// 1. **No call-graph reachability**: a helper like
///    `<FixedUInt as Integer>::gcd` exists in the archive because the
///    crate compiled it, not because any Ct fixture calls it. We can't
///    tell, from one symbol's mangled name, whether it's actually on a
///    Ct call path.
/// 2. **Public-parameter loop bounds**: helpers like
///    `<FixedUInt as ConditionallySelectable>::conditional_select`
///    contain a `for i in 0..N` loop that compiles to
///    `cmp i, #N; b.lt`. That's a forbidden mnemonic by raw regex but
///    perfectly CT-safe in context (N is a compile-time constant). A
///    static-pattern check can't distinguish that from a real
///    data-dependent branch without taint analysis.
///
/// The trade-off: we don't catch branch-injection regressions in a
/// helper that's never called from a fixture.
pub fn is_in_scope_symbol(sym: &str) -> bool {
    if sym.starts_with("ct_fix__") || sym.starts_with("_ct_fix__") {
        return true;
    }
    if sym.starts_with("nct_fix__") || sym.starts_with("_nct_fix__") {
        return true;
    }
    false
}

/// True if a `nct_fix__neg__*` symbol — the negative controls.
pub fn is_negative_control(sym: &str) -> bool {
    sym.starts_with("nct_fix__neg__") || sym.starts_with("_nct_fix__neg__")
}

/// True if a `ct_fix__*` symbol — the positive fixtures.
pub fn is_positive_fixture(sym: &str) -> bool {
    sym.starts_with("ct_fix__") || sym.starts_with("_ct_fix__")
}
