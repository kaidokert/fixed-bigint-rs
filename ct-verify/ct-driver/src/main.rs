//! Cross-target constant-time assembly gate.

mod target;

use std::path::Path;
use std::process::ExitCode;

use krabi_caliper::host::ct_asm::{run_whole_surface, DriverConfig, Surface, WholeSurfaceConfig};

fn main() -> ExitCode {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repository root");
    // Per-limb loops over public bounds leave their allowlisted helper and
    // land in fixtures once inlined (routine at opt-level "s"); accept those
    // structurally rather than by symbol.
    let targets: Vec<_> = target::TARGETS
        .iter()
        .map(|&policy| Surface {
            policy,
            counted_loops: true,
            excluded_fixtures: target::excluded_fixtures(policy.triple),
        })
        .collect();
    run_whole_surface(
        &targets,
        WholeSurfaceConfig {
            driver: DriverConfig {
                workspace,
                fixture_package: "ct-fixtures",
                fixture_features: &["heapless", "cios"],
            },
            memory_class_negatives: &[],
        },
    )
}
