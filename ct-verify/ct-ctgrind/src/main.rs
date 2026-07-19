use std::process::ExitCode;

mod fixtures_asym;
mod fixtures_cat_a;
mod fixtures_cat_b;
mod fixtures_cat_c;
mod fixtures_neg;

fn main() -> ExitCode {
    ct_fixtures::link_anchor();
    krabi_caliper::host::ctgrind::run_registered()
}
