//! Differential test against the Wasm 1.0 spec test suite.
//!
//! `tests/spec/{valid,invalid}` are binaries extracted from
//! `tests/third_party/wasm-spec` by `cargo run --example wast_extract` (see
//! that example for how "valid"/"invalid" is decided from `.wast` directives).
//! For each file, `veriwasm::validate_module` is checked against `wasmparser`
//! configured for exactly the Wasm 1.0 feature set, so a mismatch points at a
//! real divergence rather than a proposal wasmparser accepts but veriwasm
//! never claimed to.

use std::path::{Path, PathBuf};
use wasmparser::{Validator, WasmFeatures};

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn collect_wasm_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("reading {}: {e}", dir.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().and_then(|e| e.to_str()) == Some("wasm"))
        .collect();
    files.sort();
    files
}

fn wasmparser_accepts(bytes: &[u8]) -> bool {
    Validator::new_with_features(WasmFeatures::WASM1)
        .validate_all(bytes)
        .is_ok()
}

/// Files where `wasmparser` (even via the `wasm-tools validate --features
/// wasm1` CLI, so this isn't an artifact of how this test drives the crate)
/// disagrees with the spec test suite itself. `unreached-invalid_87.wasm` is
/// `br_table 0 1 1` inside unreachable code where labels 0 and 1 have
/// different result types (f32 vs f64); Wasm 1.0 requires all of a
/// `br_table`'s targets to agree regardless of reachability, but wasmparser
/// accepts it anyway. veriwasm correctly rejects it, matching the suite.
const KNOWN_WASMPARSER_DIVERGENCES: &[&str] = &["unreached-invalid_87.wasm"];

#[test]
fn spec_suite_agrees_with_wasmparser() {
    let root = workspace_root();
    let valid_dir = root.join("tests/spec/valid");
    let invalid_dir = root.join("tests/spec/invalid");

    let valid_files = collect_wasm_files(&valid_dir);
    let invalid_files = collect_wasm_files(&invalid_dir);
    assert!(
        !valid_files.is_empty() && !invalid_files.is_empty(),
        "no extracted spec tests found; run `cargo run --example wast_extract` first"
    );

    let mut bucket_mismatches = Vec::new();
    let mut veriwasm_mismatches = Vec::new();

    for (files, expected_valid) in [(&valid_files, true), (&invalid_files, false)] {
        for path in files {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let bytes = std::fs::read(path).unwrap();
            let veriwasm_valid = veriwasm::validate_module(&bytes).is_ok();

            if KNOWN_WASMPARSER_DIVERGENCES.contains(&name.as_str()) {
                if veriwasm_valid != expected_valid {
                    veriwasm_mismatches.push(format!(
                        "{name}: veriwasm says {}, but the spec suite says {}",
                        if veriwasm_valid { "valid" } else { "invalid" },
                        if expected_valid { "valid" } else { "invalid" },
                    ));
                }
                continue;
            }

            let wasmparser_valid = wasmparser_accepts(&bytes);
            if wasmparser_valid != expected_valid {
                bucket_mismatches.push(format!(
                    "{name}: extracted as {}, but wasmparser says {}",
                    if expected_valid { "valid" } else { "invalid" },
                    if wasmparser_valid { "valid" } else { "invalid" },
                ));
                continue;
            }

            if veriwasm_valid != wasmparser_valid {
                veriwasm_mismatches.push(format!(
                    "{name}: veriwasm says {}, wasmparser says {}",
                    if veriwasm_valid { "valid" } else { "invalid" },
                    if wasmparser_valid { "valid" } else { "invalid" },
                ));
            }
        }
    }

    if !bucket_mismatches.is_empty() {
        eprintln!(
            "{} files where wast_extract's bucket disagrees with wasmparser:",
            bucket_mismatches.len()
        );
        for m in &bucket_mismatches {
            eprintln!("  {m}");
        }
    }
    if !veriwasm_mismatches.is_empty() {
        eprintln!(
            "{} files where veriwasm disagrees with the expected result:",
            veriwasm_mismatches.len()
        );
        for m in &veriwasm_mismatches {
            eprintln!("  {m}");
        }
    }
    assert!(
        bucket_mismatches.is_empty() && veriwasm_mismatches.is_empty(),
        "{} bucket mismatches, {} veriwasm mismatches out of {} files",
        bucket_mismatches.len(),
        veriwasm_mismatches.len(),
        valid_files.len() + invalid_files.len(),
    );
}
