//! The WebAssembly module under Node: `js/test.mjs` drives `js/bitwright.mjs`. Skipped (with a
//! note) where Node or the `wasm32-unknown-unknown` target is missing.

use std::path::PathBuf;
use std::process::Command;

#[test]
fn the_module_under_node() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node not found: skipped");
        return;
    }
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let target_dir = manifest.parent().unwrap().join("target");
    let out = Command::new(&cargo)
        .args([
            "build",
            "--release",
            "-p",
            "bitwright-wasm",
            "--target",
            "wasm32-unknown-unknown",
        ])
        .arg("--target-dir")
        .arg(&target_dir)
        .current_dir(&manifest)
        .output()
        .expect("cargo runs");
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        if err.contains("target may not be installed")
            || err.contains("can't find crate for `core`")
        {
            eprintln!("the wasm32-unknown-unknown target is not installed: skipped");
            return;
        }
        panic!("building the module failed:\n{err}");
    }
    let wasm = target_dir.join("wasm32-unknown-unknown/release/bitwright_wasm.wasm");
    let run = Command::new("node")
        .arg(manifest.join("js/test.mjs"))
        .arg(&wasm)
        .output()
        .expect("node runs");
    assert!(
        run.status.success(),
        "{}{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "ok");
}
