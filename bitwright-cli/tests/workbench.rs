//! The Workbench (`workbench/`) reads what the command line writes: traces of the sample inputs,
//! written now, through the viewer's model and printer under Node (`workbench/test`). Skipped
//! (with a note) where Node is missing.

use std::path::PathBuf;
use std::process::Command;

fn bitwright(args: &[&str]) {
    let out = Command::new(env!("CARGO_BIN_EXE_bitwright"))
        .args(args)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "bitwright {args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn the_workbench_reads_fresh_traces() {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("node not found: skipped");
        return;
    }
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let samples = root.join("workbench/samples");
    let tmp = PathBuf::from(env!("CARGO_TARGET_TMPDIR"));
    let part = |name: &str| tmp.join(name).to_string_lossy().into_owned();
    let path = |p: PathBuf| p.to_string_lossy().into_owned();
    bitwright(&[
        "simplify",
        "--width",
        "32",
        "--file",
        &path(samples.join("corpus-32.txt")),
        "--trace",
        &part("wb-32.bwt"),
    ]);
    bitwright(&[
        "simplify",
        "--width",
        "64",
        "--file",
        &path(samples.join("corpus-64.txt")),
        "--trace",
        &part("wb-64.bwt"),
    ]);
    bitwright(&[
        "simplify",
        "--width",
        "64",
        "--assume",
        "rsp & 15 == 0",
        "--assume",
        "idx <u n",
        "--trace",
        &part("wb-assume.bwt"),
        "--",
        "((rsp + 32) & 15) + zext<64>(idx <=u n)",
    ]);
    let mut all = String::new();
    for p in ["wb-32.bwt", "wb-64.bwt", "wb-assume.bwt"] {
        all.push_str(&std::fs::read_to_string(tmp.join(p)).unwrap());
    }
    let trace = tmp.join("wb-all.bwt");
    std::fs::write(&trace, all).unwrap();
    let out = Command::new("node")
        .arg("--test")
        .arg(root.join("workbench/test/model.test.mjs"))
        .env("BWT", &trace)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "the Workbench's model tests failed:\n{}\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}
