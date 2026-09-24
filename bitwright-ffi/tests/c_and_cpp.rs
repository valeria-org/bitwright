//! Compiles the C and C++ examples with the system compilers (`$CC`, default `cc`; `$CXX`,
//! default `c++`), strict warnings on, links them against the library this package builds, and
//! checks what they print.
#![cfg(unix)]

use std::path::{Path, PathBuf};
use std::process::Command;

const C_EXPECTED: &str = "\
simplified: x + y
f(100) = 45
known zero 0x0e, known one 0x01, range [1, 241]
a <u 16 proves a & 0xf0 == 0: yes (relies on 0x1)
error 9: expected an expression (at bytes 3..3)
";

const CPP_EXPECTED: &str = "\
x + y
x
x == 0xd3220fb78e33751f
x + y
(2^64)^2 + 1 mod 2^128 = 0x1:128
known zero 0xe:8, range [0x1:8, 0xf1:8]
b <u 16 proves (b & 0xf0) == 0: yes
x + y has 2 children: x, y
error 9: expected an expression (at bytes 3..3)
";

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Where cargo put `libbitwright` for this test: `deps/`, next to the test (`cargo build`
/// copies it up one level, `cargo test` does not).
fn lib_dir() -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    let dir = exe.parent().unwrap().to_path_buf();
    let lib = dir.join(format!("libbitwright{}", std::env::consts::DLL_SUFFIX));
    assert!(lib.exists(), "no {}", lib.display());
    dir
}

fn compiler(var: &str, default: &str) -> String {
    std::env::var(var).unwrap_or_else(|_| default.to_string())
}

fn run(cmd: &mut Command) -> String {
    let out = cmd
        .output()
        .unwrap_or_else(|e| panic!("cannot run {cmd:?}: {e}"));
    assert!(
        out.status.success(),
        "{cmd:?} failed:\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).unwrap()
}

/// Compiles `source` with `cc` and `flags` against the shared library, and runs it.
fn build_and_run(cc: &str, flags: &[&str], source: &Path, name: &str) -> String {
    let lib = lib_dir();
    let exe = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    run(Command::new(cc)
        .args(flags)
        .args(["-Wall", "-Wextra", "-pedantic", "-Werror", "-I"])
        .arg(manifest().join("include"))
        .arg(source)
        .arg("-L")
        .arg(&lib)
        .arg(format!("-Wl,-rpath,{}", lib.display()))
        .args(["-lbitwright", "-o"])
        .arg(&exe));
    run(&mut Command::new(&exe))
}

#[test]
fn the_c_example() {
    let cc = compiler("CC", "cc");
    let src = manifest().join("examples/simplify.c");
    for std in ["-std=c99", "-std=c11"] {
        let out = build_and_run(&cc, &[std], &src, &format!("simplify-c-{std}"));
        assert_eq!(out, C_EXPECTED, "{std}");
    }
}

#[test]
fn the_cpp_example() {
    let cxx = compiler("CXX", "c++");
    let src = manifest().join("examples/simplify.cpp");
    for std in ["-std=c++17", "-std=c++20"] {
        let out = build_and_run(&cxx, &[std], &src, &format!("simplify-cpp-{std}"));
        assert_eq!(out, CPP_EXPECTED, "{std}");
    }
}

/// The C header compiles as C++ too (inside `extern "C"`).
#[test]
fn the_c_example_as_cpp() {
    let cxx = compiler("CXX", "c++");
    let src = manifest().join("examples/simplify.c");
    let out = build_and_run(
        &cxx,
        &["-x", "c++", "-std=c++17"],
        &src,
        "simplify-c-as-cpp",
    );
    assert_eq!(out, C_EXPECTED);
}

/// The static library links with the system libraries Rust's standard library needs.
#[cfg(target_os = "linux")]
#[test]
fn the_static_library() {
    let cc = compiler("CC", "cc");
    let lib = lib_dir();
    let exe = Path::new(env!("CARGO_TARGET_TMPDIR")).join("simplify-c-static");
    run(Command::new(&cc)
        .args(["-std=c99", "-I"])
        .arg(manifest().join("include"))
        .arg(manifest().join("examples/simplify.c"))
        .arg(lib.join("libbitwright.a"))
        .args(["-lpthread", "-ldl", "-lm", "-o"])
        .arg(&exe));
    assert_eq!(run(&mut Command::new(&exe)), C_EXPECTED);
}

/// The code blocks of `lang` in the book's chapter on the bindings.
fn book_blocks(lang: &str) -> Vec<String> {
    let chapter = std::fs::read_to_string(manifest().join("../book/src/bindings.md")).unwrap();
    let fence = format!("```{lang}\n");
    chapter
        .split(&fence)
        .skip(1)
        .map(|rest| rest.split("```\n").next().unwrap().to_string())
        .collect()
}

/// Every C and C++ example of the book compiles and runs (its checks are `assert`s).
#[test]
fn the_book_examples() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"));
    for (lang, cc, std, ext) in [
        ("c", compiler("CC", "cc"), "-std=c99", "c"),
        ("cpp", compiler("CXX", "c++"), "-std=c++17", "cpp"),
    ] {
        let blocks = book_blocks(lang);
        assert!(!blocks.is_empty(), "no {lang} examples in the book");
        for (i, code) in blocks.iter().enumerate() {
            let src = dir.join(format!("book-{i}.{ext}"));
            std::fs::write(&src, code).unwrap();
            build_and_run(&cc, &[std], &src, &format!("book-{lang}-{i}"));
        }
    }
}
