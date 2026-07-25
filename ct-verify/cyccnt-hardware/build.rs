use std::{env, fs, path::PathBuf};

fn main() {
    let target = env::var("TARGET").expect("TARGET not set");
    // Excluded from workspace default-members, so this only runs if someone
    // explicitly builds the crate for the wrong target. Emit a clean build
    // error (no panic backtrace) pointing at the required target.
    if target != "thumbv7em-none-eabihf" {
        println!(
            "cargo::error=fixed-bigint-cyccnt-hardware is bare-metal; build it with \
             --target thumbv7em-none-eabihf (the STM32F407 rig target)."
        );
        return;
    }

    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR not set"));
    fs::copy("memory.x", out.join("memory.x")).expect("copy memory.x");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rerun-if-changed=memory.x");
    println!("cargo:rustc-link-arg=--nmagic");
    println!("cargo:rustc-link-arg=-Tlink.x");
}
