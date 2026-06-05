//! CT-verify driver.
//!
//! Workflow per target:
//!   1. cargo build --release --target=<triple> -p ct-fixtures
//!   2. find the resulting libct_fixtures.a
//!   3. llvm-objdump --disassemble + filter to in-scope symbols
//!   4. run per-target mnemonic check (forbidden / allowed / thumb IT)
//!   5. emit JSON report
//!   6. exit non-zero if any ct_fix__* fixture has a violation
//!      OR any nct_fix__neg__* fixture has zero violations

mod mnemonics;
mod parse;
mod report;
mod target;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use crate::parse::{Patterns, Violation};
use crate::report::{Report, ViolationOut};
use crate::target::{lookup, TargetSpec, TARGETS};

#[derive(Default)]
struct Args {
    target: Option<String>,
    json_out: Option<PathBuf>,
    list_targets: bool,
    skip_build: bool,
    archive_override: Option<PathBuf>,
}

fn parse_args() -> Result<Args, String> {
    let mut args = Args::default();
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--target" => {
                args.target = Some(it.next().ok_or("--target requires a triple")?);
            }
            "--json-out" => {
                args.json_out = Some(PathBuf::from(
                    it.next().ok_or("--json-out requires a path")?,
                ));
            }
            "--list-targets" => args.list_targets = true,
            "--skip-build" => args.skip_build = true,
            "--archive" => {
                args.archive_override =
                    Some(PathBuf::from(it.next().ok_or("--archive requires a path")?));
            }
            "-h" | "--help" => {
                print_help();
                std::process::exit(0);
            }
            other => return Err(format!("unknown argument: {}", other)),
        }
    }
    Ok(args)
}

fn print_help() {
    eprintln!(
        "ct-driver — disassemble ct-fixtures and gate on forbidden conditional branches.\n\
         \n\
         Usage:\n\
           ct-driver --target <TRIPLE> [--json-out <PATH>] [--skip-build] [--archive <PATH>]\n\
           ct-driver --list-targets\n\
           ct-driver -h | --help\n\
         \n\
         Options:\n\
           --target <TRIPLE>   Cargo target triple to verify (use --list-targets for the list).\n\
                               If omitted, the host triple (rustc -vV → host) is used.\n\
           --json-out <PATH>   Write JSON report to PATH (also written to stdout in human form).\n\
           --skip-build        Don't run cargo build; reuse the existing libct_fixtures.a.\n\
           --archive <PATH>    Override the path to libct_fixtures.a (for debugging).\n\
         \n\
         Exit code 0 = clean. Non-zero = ct violations OR negative controls didn't trip."
    );
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {}", e);
            print_help();
            return ExitCode::from(2);
        }
    };

    if args.list_targets {
        for t in TARGETS {
            println!(
                "[{}] {}  (toolchain: {})",
                t.priority, t.triple, t.toolchain
            );
        }
        return ExitCode::SUCCESS;
    }

    let triple = args
        .target
        .clone()
        .unwrap_or_else(|| host_triple().unwrap_or_else(|| "x86_64-unknown-linux-gnu".to_string()));

    let Some(spec) = lookup(&triple) else {
        eprintln!(
            "error: unknown target triple '{}'. Use --list-targets to see supported ones.",
            triple
        );
        return ExitCode::from(2);
    };

    // 1. Build (unless skipped).
    if !args.skip_build {
        if let Err(e) = cargo_build_fixtures(spec) {
            eprintln!("error: cargo build failed: {}", e);
            return ExitCode::from(3);
        }
    }

    // 2. Locate the staticlib.
    let archive = if let Some(p) = args.archive_override.clone() {
        p
    } else {
        match find_archive(spec) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("error: locating libct_fixtures.a: {}", e);
                return ExitCode::from(3);
            }
        }
    };

    // 3. Disassemble.
    let objdump_text = match run_objdump(spec, &archive) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("error: llvm-objdump failed: {}", e);
            return ExitCode::from(3);
        }
    };

    // 4. Parse + scan.
    let blocks = parse::split_blocks(&objdump_text);
    let pat = Patterns::build(spec);
    // Reachability: fixtures plus every helper transitively reachable
    // through call edges. Helpers that aren't reached from any fixture
    // are out of scope (probably dead code in the staticlib).
    let reachable = parse::compute_reachable_symbols(&blocks, &pat.call);

    let mut ct_fixture_count: usize = 0;
    let mut ct_violations: Vec<Violation> = Vec::new();
    let mut neg_tripped: BTreeSet<String> = BTreeSet::new();
    let mut neg_seen: BTreeSet<String> = BTreeSet::new();
    let mut helper_violations: Vec<Violation> = Vec::new();
    let mut helpers_scanned: usize = 0;
    let mut helpers_allowlisted: usize = 0;

    for block in &blocks {
        // Fixtures: scan all (positive + negative). Negative-control
        // bodies are expected to contain forbidden mnemonics.
        if parse::is_positive_fixture(&block.symbol) {
            ct_fixture_count += 1;
            ct_violations.extend(parse::scan_block(block, spec, &pat));
            continue;
        }
        if parse::is_negative_control(&block.symbol) {
            let canonical = block.symbol.trim_start_matches('_').to_string();
            neg_seen.insert(canonical.clone());
            if !parse::scan_block(block, spec, &pat).is_empty() {
                neg_tripped.insert(canonical);
            }
            continue;
        }

        // Helper reached transitively from a Ct fixture. Skip if it
        // matches the per-target allowlist (public-parameter loop
        // class).
        if !reachable.contains(&block.symbol) {
            continue;
        }
        if parse::is_allowed_helper(&block.symbol, &pat.allowed_helpers) {
            helpers_allowlisted += 1;
            continue;
        }
        helpers_scanned += 1;
        helper_violations.extend(parse::scan_block(block, spec, &pat));
    }
    let neg_fixture_count = neg_seen.len();
    let neg_failed: Vec<String> = neg_seen.difference(&neg_tripped).cloned().collect();

    // 5. Emit report.
    let report = Report {
        target: triple.clone(),
        fixtures_checked: ct_fixture_count,
        negative_controls_checked: neg_fixture_count,
        helpers_scanned,
        helpers_allowlisted,
        ct_violations: ct_violations.into_iter().map(ViolationOut::from).collect(),
        helper_violations: helper_violations
            .into_iter()
            .map(ViolationOut::from)
            .collect(),
        negative_controls_failed_to_trip: neg_failed,
    };
    report.print_human();

    if let Some(path) = args.json_out.as_ref() {
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        match std::fs::File::create(path) {
            Ok(f) => {
                if let Err(e) = serde_json::to_writer_pretty(f, &report) {
                    eprintln!("warning: writing JSON report failed: {}", e);
                }
            }
            Err(e) => eprintln!("warning: creating JSON report file failed: {}", e),
        }
    }

    // Empty fixture sets mean the harness lost contact with the
    // archive — silent self-test failure. Treat as hard fail.
    if ct_fixture_count == 0 {
        eprintln!("error: no ct_fix__* fixtures found in archive — harness self-test failed");
        return ExitCode::FAILURE;
    }
    if neg_fixture_count == 0 {
        eprintln!("error: no nct_fix__neg__* negative controls found in archive — harness self-test failed");
        return ExitCode::FAILURE;
    }

    if report.exit_code() == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

fn host_triple() -> Option<String> {
    let out = Command::new("rustc").arg("-vV").output().ok()?;
    let s = String::from_utf8_lossy(&out.stdout);
    for line in s.lines() {
        if let Some(rest) = line.strip_prefix("host: ") {
            return Some(rest.trim().to_string());
        }
    }
    None
}

fn cargo_build_fixtures(spec: &TargetSpec) -> Result<(), String> {
    let host = host_triple().unwrap_or_default();
    let mut cmd = Command::new(env!("CARGO"));
    cmd.arg("build")
        .arg("--release")
        .arg("-p")
        .arg("ct-fixtures");

    // Only pass --target if it differs from host (otherwise we end up
    // building in `target/release/` rather than `target/<triple>/release/`,
    // which find_archive accounts for, but passing --target=host is also
    // fine and produces the per-triple path).
    if spec.triple != host {
        cmd.arg("--target").arg(spec.triple);
    }
    for a in spec.extra_cargo_args {
        cmd.arg(a);
    }

    eprintln!(
        "[ct-driver] cargo {}",
        cmd.get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(" ")
    );
    let status = cmd.status().map_err(|e| e.to_string())?;
    if !status.success() {
        return Err(format!("cargo build exited with {}", status));
    }
    Ok(())
}

fn workspace_target_dir() -> PathBuf {
    // Find the workspace target dir. We're a workspace member at
    // `<root>/ct-verify/ct-driver/`, so target dir is `<root>/target/`.
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // Walk up two levels: ct-driver -> ct-verify -> root, then add target.
    let root = manifest
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .unwrap_or(manifest);
    root.join("target")
}

fn find_archive(spec: &TargetSpec) -> Result<PathBuf, String> {
    let host = host_triple().unwrap_or_default();
    let target_dir = workspace_target_dir();
    let archive_subpath = "release/libct_fixtures.a";

    let candidates: Vec<PathBuf> = if spec.triple == host {
        vec![
            target_dir.join(archive_subpath),
            target_dir.join(spec.triple).join(archive_subpath),
        ]
    } else {
        vec![target_dir.join(spec.triple).join(archive_subpath)]
    };

    for c in &candidates {
        if c.exists() {
            return Ok(c.clone());
        }
    }
    Err(format!(
        "could not find libct_fixtures.a — tried: {}",
        candidates
            .iter()
            .map(|p| p.display().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    ))
}

fn llvm_objdump_path() -> Result<PathBuf, String> {
    // Prefer the llvm-tools-preview component (matches the toolchain).
    if let Ok(out) = Command::new("rustc").arg("--print").arg("sysroot").output() {
        if out.status.success() {
            let sysroot = String::from_utf8_lossy(&out.stdout).trim().to_string();
            // The llvm-tools-preview component installs binaries under
            //   <sysroot>/lib/rustlib/<host>/bin/llvm-objdump
            let host = host_triple().unwrap_or_default();
            let candidate = Path::new(&sysroot)
                .join("lib")
                .join("rustlib")
                .join(&host)
                .join("bin")
                .join("llvm-objdump");
            if candidate.exists() {
                return Ok(candidate);
            }
        }
    }
    // Fall back to PATH lookup at exec time. If neither name resolves
    // run_objdump will surface a clear "No such file" error.
    Ok(PathBuf::from("llvm-objdump"))
}

fn run_objdump(spec: &TargetSpec, archive: &Path) -> Result<String, String> {
    let tool = llvm_objdump_path()?;
    let arch_flag = arch_flag_for(spec.triple);

    let mut cmd = Command::new(&tool);
    cmd.arg("--disassemble")
        .arg("--no-show-raw-insn")
        .arg("--no-leading-addr")
        // `-r` interleaves relocation entries with the disassembly. The
        // reachability walker reads these to resolve `bl` / `call` /
        // `jal` targets — in a static archive they're unresolved at
        // disassembly time and otherwise print as self-relative
        // placeholders like `bl 0x6c70 <self+0x10>`.
        .arg("--reloc");
    if let Some(arch) = arch_flag {
        cmd.arg(format!("--triple={}", arch));
    }
    cmd.arg(archive);

    let out = cmd.output().map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!(
            "llvm-objdump failed: status={} stderr={}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

fn arch_flag_for(triple: &str) -> Option<&'static str> {
    // llvm-objdump usually infers the architecture from the object file,
    // but for some targets (notably AVR) we need to be explicit.
    if triple.starts_with("avr-") {
        Some("avr")
    } else {
        None
    }
}
