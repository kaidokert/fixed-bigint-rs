//! Report shape (JSON + human).
//!
//! The driver emits one JSON file per target plus a stdout summary.

use serde::Serialize;

use crate::parse::Violation;

#[derive(Debug, Serialize)]
pub struct Report {
    pub target: String,
    pub fixtures_checked: usize,
    pub negative_controls_checked: usize,
    pub helpers_scanned: usize,
    pub helpers_allowlisted: usize,
    pub ct_violations: Vec<ViolationOut>,
    /// Violations found in helpers (functions called transitively from
    /// fixtures, not the fixture wrappers themselves). Kept separate so
    /// reviewers can see at a glance whether a regression is in a Ct
    /// primitive's own body or in a helper it pulls in.
    pub helper_violations: Vec<ViolationOut>,
    pub negative_controls_failed_to_trip: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct ViolationOut {
    pub symbol: String,
    pub offset: String, // hex
    pub insn: String,
    pub context: Vec<String>,
}

impl From<Violation> for ViolationOut {
    fn from(v: Violation) -> Self {
        Self {
            symbol: v.symbol,
            offset: format!("0x{:x}", v.offset),
            insn: v.line.trim().to_string(),
            context: v.context,
        }
    }
}

impl Report {
    pub fn exit_code(&self) -> i32 {
        if !self.ct_violations.is_empty()
            || !self.helper_violations.is_empty()
            || !self.negative_controls_failed_to_trip.is_empty()
        {
            1
        } else {
            0
        }
    }

    pub fn print_human(&self) {
        println!("==== CT-verify report for {} ====", self.target);
        println!(
            "  ct_fix__*       fixtures checked: {}",
            self.fixtures_checked
        );
        println!(
            "  nct_fix__neg__* controls checked: {}",
            self.negative_controls_checked
        );
        println!(
            "  helpers scanned (reachable):      {} ({} allowlisted)",
            self.helpers_scanned, self.helpers_allowlisted
        );
        if self.ct_violations.is_empty() {
            println!("  Ct violations (fixture):          0  ✓");
        } else {
            println!(
                "  Ct violations (fixture):          {}  ✗",
                self.ct_violations.len()
            );
            for v in &self.ct_violations {
                println!("    [{}] {} {}", v.offset, v.symbol, v.insn);
                for ctx in &v.context {
                    println!("        | {}", ctx.trim());
                }
            }
        }
        if self.helper_violations.is_empty() {
            println!("  Ct violations (helper):           0  ✓");
        } else {
            println!(
                "  Ct violations (helper):           {}  ✗",
                self.helper_violations.len()
            );
            for v in &self.helper_violations {
                println!("    [{}] {} {}", v.offset, v.symbol, v.insn);
                for ctx in &v.context {
                    println!("        | {}", ctx.trim());
                }
            }
        }
        if self.negative_controls_failed_to_trip.is_empty() {
            println!("  Negative controls tripped:        all ✓");
        } else {
            println!(
                "  Negative controls FAILED to trip: {}  ✗",
                self.negative_controls_failed_to_trip.len()
            );
            for s in &self.negative_controls_failed_to_trip {
                println!("    {} (expected ≥1 forbidden mnemonic, found 0)", s);
            }
        }
    }
}
