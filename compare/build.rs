//! With the feature `native-smt`, where the `versus-smt` binary finds z3 and Bitwuzla: `Z3_DIR`
//! is an unpacked z3 release (`bin/libz3.so`), `BITWUZLA_DIR` an unpacked Bitwuzla static
//! release (`lib/x86_64-linux-gnu/libbitwuzla.a`). Without the feature, nothing is linked.

fn main() {
    println!("cargo:rerun-if-env-changed=Z3_DIR");
    println!("cargo:rerun-if-env-changed=BITWUZLA_DIR");
    if std::env::var_os("CARGO_FEATURE_NATIVE_SMT").is_none() {
        return;
    }
    let dir = |var: &str| {
        std::env::var(var).unwrap_or_else(|_| {
            panic!("the feature `native-smt` needs {var} (see compare/README.md)")
        })
    };
    let (z3, bitwuzla) = (dir("Z3_DIR"), dir("BITWUZLA_DIR"));
    println!("cargo:rustc-link-search=native={z3}/bin");
    println!("cargo:rustc-link-arg-bin=versus-smt=-Wl,-rpath,{z3}/bin");
    println!("cargo:rustc-link-search=native={bitwuzla}/lib/x86_64-linux-gnu");
    println!("cargo:rustc-link-search=native={bitwuzla}/lib");
}
