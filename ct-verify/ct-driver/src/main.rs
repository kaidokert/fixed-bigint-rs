//! Cross-target constant-time assembly gate.

mod target;

use std::path::Path;
use std::process::ExitCode;

use krabi_caliper::host::ct_asm::{DriverConfig, WholeSurfaceConfig, run_whole_surface};

fn main() -> ExitCode {
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("repository root");
    run_whole_surface(
        target::TARGETS,
        WholeSurfaceConfig {
            driver: DriverConfig {
                workspace,
                fixture_package: "ct-fixtures",
                fixture_features: &[],
            },
            memory_class_negatives: &[],
        },
    )
}
