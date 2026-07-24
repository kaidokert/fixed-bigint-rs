use std::{env, fs, path::PathBuf};

fn main() {
    let target = env::var("TARGET").expect("TARGET not set");
    assert_eq!(
        target, "thumbv7em-none-eabihf",
        "J-Trace fixture requires the STM32F407 target"
    );

    let out = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR not set"));
    fs::copy("memory.x", out.join("memory.x")).expect("copy memory.x");
    println!("cargo:rustc-link-search={}", out.display());
    println!("cargo:rerun-if-changed=memory.x");
    println!("cargo:rustc-link-arg=--nmagic");
    println!("cargo:rustc-link-arg=-Tlink.x");
}
