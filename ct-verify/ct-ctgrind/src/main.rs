use std::process::ExitCode;

krabi_caliper::ctgrind_standard_controls!();

fn main() -> ExitCode {
    ct_fixtures::link_anchor();
    krabi_caliper::host::ctgrind::run_registered()
}
