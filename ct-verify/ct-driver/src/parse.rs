//! Disassembly parser.
//!
//! Takes the textual output of `llvm-objdump --disassemble
//! --no-show-raw-insn --no-leading-addr` and splits it into per-symbol
//! function blocks. Then for each block runs the per-target mnemonic
//! check + the thumb IT-state machine + the unconditional-branch
//! direction classifier.

use std::collections::{HashMap, HashSet, VecDeque};
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

// Relocation line emitted by `objdump -r`, interleaved with disassembly.
// Format varies by file format:
//   Mach-O: `\t\t<addr>:  ARM64_RELOC_BRANCH26\t<symbol>`
//   ELF:    `\t\t<addr>: R_AARCH64_CALL26\t<symbol>` (and other R_*)
// Common shape: indented line, optional `addr:`, a relocation type
// (token containing `RELOC` or starting with `R_`), then a symbol.
static RELOC_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"^\s+(?:[0-9a-fA-F]+:)?\s*(?:[A-Z][A-Z0-9_]*_RELOC_[A-Z0-9_]+|R_[A-Z0-9_]+)\s+(\S+)\s*$",
    )
    .unwrap()
});

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
    /// When the instruction has a relocation entry resolving its
    /// operand (a `bl`/`call`/`jal` target, typically), the relocation
    /// symbol name. `None` for non-call instructions and for indirect
    /// or fully-resolved operands.
    pub call_target: Option<String>,
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

        // Relocation lines look superficially like instruction lines
        // (they have an `address:` prefix), so match them first and
        // attach the symbol to the previous instruction.
        if let Some(caps) = RELOC_RE.captures(line) {
            if let Some(last) = block.insns.last_mut() {
                if last.call_target.is_none() {
                    last.call_target = caps.get(1).map(|m| normalize_call_target(m.as_str()));
                }
            }
            continue;
        }

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
                call_target: None,
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
    pub call: Vec<Regex>,
    pub allowed_helpers: Vec<Regex>,
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
            call: spec
                .call_mnemonics
                .iter()
                .map(|p| Regex::new(p).expect("bad call regex"))
                .collect(),
            allowed_helpers: spec
                .allowed_helpers
                .iter()
                .map(|p| Regex::new(p).expect("bad allowed_helpers regex"))
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

/// Compute the transitive call-reachability closure starting from each
/// Ct fixture symbol (`ct_fix__*`). Negative-control fixtures are
/// deliberately excluded — their bodies invoke Nct helpers that have
/// branchful behaviour by design, and we don't want those helpers
/// flagged. The returned set is `{ct_fixtures} ∪ {helpers reached from
/// any ct_fixture via call edges}`.
///
/// External targets (symbols not present as `FunctionBlock`s in
/// `blocks`) and indirect calls (no resolved relocation or `<sym>`
/// operand) are silently dropped — those are outside our scope.
pub fn compute_reachable_symbols(
    blocks: &[FunctionBlock],
    call_patterns: &[Regex],
) -> HashSet<String> {
    let blocks_by_sym: HashMap<&str, &FunctionBlock> =
        blocks.iter().map(|b| (b.symbol.as_str(), b)).collect();

    let mut visited: HashSet<String> = HashSet::new();
    let mut queue: VecDeque<String> = blocks
        .iter()
        .filter(|b| is_positive_fixture(&b.symbol))
        .map(|b| b.symbol.clone())
        .collect();

    while let Some(sym) = queue.pop_front() {
        if !visited.insert(sym.clone()) {
            continue;
        }
        let Some(block) = blocks_by_sym.get(sym.as_str()) else {
            // External symbol or stripped target — outside our scope.
            continue;
        };
        for insn in &block.insns {
            if !call_patterns.iter().any(|re| re.is_match(&insn.mnemonic)) {
                continue;
            }
            // Prefer the relocation-resolved target (covers unresolved
            // calls in the staticlib); fall back to the inline
            // `<symbol>` annotation for already-linked binaries.
            let target = insn
                .call_target
                .clone()
                .or_else(|| extract_call_target(&insn.full_line));
            if let Some(target) = target {
                if !visited.contains(&target) {
                    queue.push_back(target);
                }
            }
        }
    }
    visited
}

/// Pull a resolved call target out of an objdump line. Objdump prints
/// the resolved symbol as `<symbol_name>` after the instruction operands
/// when the call has a known target in the same disassembly unit;
/// indirect calls (e.g. `blr x0`) and unresolved targets don't get a
/// `<...>` suffix and return `None`.
fn extract_call_target(full_line: &str) -> Option<String> {
    // Match `<symbol>` near the end of the line, tolerating a trailing
    // `@ imm = #0x…` annotation that thumb objdump appends.
    static TARGET_RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"<([^>]+)>(?:\s+@\s+imm[^<]*)?\s*$").unwrap());
    TARGET_RE
        .captures(full_line.trim_end())
        .and_then(|c| c.get(1))
        .map(|m| normalize_call_target(m.as_str()))
}

/// Strip addend / PLT / GOT decorations that objdump appends to call
/// targets, so the result matches the bare-name keys in
/// `blocks_by_sym`. Examples that need normalising:
///
/// - `_ZN…count_ones…E-0x4`       (ELF `R_X86_64_GOTPCREL` addend)
/// - `<some_helper+0x10>`         (inline `<>` tag with non-zero offset)
/// - `memcpy@plt`                 (PLT decoration)
/// - `__some_sym@GOTPCREL`        (GOT / reloc-type decoration)
///
/// Truncate at the first `+`, `-`, `@`, or whitespace and return the
/// prefix.
fn normalize_call_target(raw: &str) -> String {
    let cutoff = raw
        .find(|c: char| c == '+' || c == '-' || c == '@' || c.is_whitespace())
        .unwrap_or(raw.len());
    raw[..cutoff].to_string()
}

/// Check whether a symbol matches any of the per-target helper
/// allowlist patterns (public-parameter loops we've classified as
/// CT-safe by inspection).
pub fn is_allowed_helper(sym: &str, allowed_helpers: &[Regex]) -> bool {
    allowed_helpers.iter().any(|re| re.is_match(sym))
}

/// True if a `nct_fix__neg__*` symbol — the negative controls.
pub fn is_negative_control(sym: &str) -> bool {
    sym.starts_with("nct_fix__neg__") || sym.starts_with("_nct_fix__neg__")
}

/// True if a `ct_fix__*` symbol — the positive fixtures.
pub fn is_positive_fixture(sym: &str) -> bool {
    sym.starts_with("ct_fix__") || sym.starts_with("_ct_fix__")
}
