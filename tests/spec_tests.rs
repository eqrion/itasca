//! Differential test against the Wasm 1.0 spec test suite.
//!
//! `tests/spec/{valid,invalid}` are binaries extracted from
//! `tests/third_party/wasm-spec` by `cargo run --example wast_extract` (see
//! that example for how "valid"/"invalid" is decided from `.wast` directives).
//! For each file, `itasca::validate_module` is checked against `wasmparser`
//! configured for exactly the Wasm 1.0 feature set, so a mismatch points at a
//! real divergence rather than a proposal wasmparser accepts but itasca
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
/// accepts it anyway. itasca correctly rejects it, matching the suite.
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
    let mut itasca_mismatches = Vec::new();

    for (files, expected_valid) in [(&valid_files, true), (&invalid_files, false)] {
        for path in files {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let bytes = std::fs::read(path).unwrap();
            let itasca_valid = itasca::validate_module(&bytes).is_ok();

            if KNOWN_WASMPARSER_DIVERGENCES.contains(&name.as_str()) {
                if itasca_valid != expected_valid {
                    itasca_mismatches.push(format!(
                        "{name}: itasca says {}, but the spec suite says {}",
                        if itasca_valid { "valid" } else { "invalid" },
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

            if itasca_valid != wasmparser_valid {
                itasca_mismatches.push(format!(
                    "{name}: itasca says {}, wasmparser says {}",
                    if itasca_valid { "valid" } else { "invalid" },
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
    if !itasca_mismatches.is_empty() {
        eprintln!(
            "{} files where itasca disagrees with the expected result:",
            itasca_mismatches.len()
        );
        for m in &itasca_mismatches {
            eprintln!("  {m}");
        }
    }
    assert!(
        bucket_mismatches.is_empty() && itasca_mismatches.is_empty(),
        "{} bucket mismatches, {} itasca mismatches out of {} files",
        bucket_mismatches.len(),
        itasca_mismatches.len(),
        valid_files.len() + invalid_files.len(),
    );
}

// --- The types a validated module reports for its imports and exports ---
//
// `import_types` / `export_types` are what an embedder links against, so they
// are checked the same way as accept/reject: against wasmparser over the same
// corpus. Both sides are projected to a small string form, so a mismatch reads
// clearly and the comparison doesn't depend on either crate's type layout.

fn valtype(t: itasca::types::ValueType) -> &'static str {
    use itasca::types::ValueType;
    match t {
        ValueType::I32 => "i32",
        ValueType::I64 => "i64",
        ValueType::F32 => "f32",
        ValueType::F64 => "f64",
    }
}

fn limits(min: u64, max: Option<u64>) -> String {
    match max {
        Some(m) => format!("{min}..{m}"),
        None => format!("{min}.."),
    }
}

fn ours(t: &itasca::ExternType) -> String {
    use itasca::types::Mut;
    use itasca::ExternType;
    match t {
        ExternType::Func(ft) => {
            let ps: Vec<&str> = ft.params.iter().map(|t| valtype(*t)).collect();
            let rs: Vec<&str> = ft.results.iter().map(|t| valtype(*t)).collect();
            format!("func({})->({})", ps.join(","), rs.join(","))
        }
        ExternType::Table(tt) => format!(
            "table funcref {}",
            limits(tt.limits.min.into(), tt.limits.max.map(u64::from))
        ),
        ExternType::Memory(mt) => format!(
            "memory {}",
            limits(mt.limits.min.into(), mt.limits.max.map(u64::from))
        ),
        ExternType::Global(gt) => format!(
            "global {} {}",
            if gt.mutability == Mut::Var {
                "var"
            } else {
                "const"
            },
            valtype(gt.valtype)
        ),
    }
}

fn wp_valtype(t: wasmparser::ValType) -> &'static str {
    use wasmparser::ValType;
    match t {
        ValType::I32 => "i32",
        ValType::I64 => "i64",
        ValType::F32 => "f32",
        ValType::F64 => "f64",
        _ => panic!("not a Wasm 1.0 value type"),
    }
}

fn wp_func(ft: &wasmparser::FuncType) -> String {
    let ps: Vec<&str> = ft.params().iter().map(|t| wp_valtype(*t)).collect();
    let rs: Vec<&str> = ft.results().iter().map(|t| wp_valtype(*t)).collect();
    format!("func({})->({})", ps.join(","), rs.join(","))
}

fn wp_table(tt: &wasmparser::TableType) -> String {
    format!("table funcref {}", limits(tt.initial, tt.maximum))
}

fn wp_memory(mt: &wasmparser::MemoryType) -> String {
    format!("memory {}", limits(mt.initial, mt.maximum))
}

fn wp_global(gt: &wasmparser::GlobalType) -> String {
    format!(
        "global {} {}",
        if gt.mutable { "var" } else { "const" },
        wp_valtype(gt.content_type)
    )
}

/// The import and export types wasmparser assigns, in declaration order.
/// `None` if it rejects the module or the module reaches past Wasm 1.0.
fn wasmparser_extern_types(bytes: &[u8]) -> Option<(Vec<String>, Vec<String>)> {
    use wasmparser::{ExternalKind, Parser, Payload, TypeRef};

    let types = Validator::new_with_features(WasmFeatures::WASM1)
        .validate_all(bytes)
        .ok()?;
    let spaces = types.as_ref();
    let mut imports = Vec::new();
    let mut exports = Vec::new();

    for payload in Parser::new(0).parse_all(bytes) {
        match payload.ok()? {
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    imports.push(match import.ok()?.ty {
                        TypeRef::Func(i) => {
                            wp_func(types[spaces.core_type_at_in_module(i)].unwrap_func())
                        }
                        TypeRef::Table(tt) => wp_table(&tt),
                        TypeRef::Memory(mt) => wp_memory(&mt),
                        TypeRef::Global(gt) => wp_global(&gt),
                        _ => return None,
                    });
                }
            }
            Payload::ExportSection(reader) => {
                for export in reader {
                    let export = export.ok()?;
                    exports.push(match export.kind {
                        ExternalKind::Func => {
                            wp_func(types[spaces.core_function_at(export.index)].unwrap_func())
                        }
                        ExternalKind::Table => wp_table(&spaces.table_at(export.index)),
                        ExternalKind::Memory => wp_memory(&spaces.memory_at(export.index)),
                        ExternalKind::Global => wp_global(&spaces.global_at(export.index)),
                        _ => return None,
                    });
                }
            }
            _ => {}
        }
    }
    Some((imports, exports))
}

#[test]
fn extern_types_agree_with_wasmparser() {
    let root = workspace_root();
    let files = collect_wasm_files(&root.join("tests/spec/valid"));
    assert!(
        !files.is_empty(),
        "no extracted spec tests found; run `cargo run --example wast_extract` first"
    );

    let mut mismatches = Vec::new();
    let mut with_imports = 0usize;
    let mut with_exports = 0usize;

    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let bytes = std::fs::read(path).unwrap();
        let Ok(module) = itasca::validate_module(&bytes) else {
            continue;
        };
        let Some((their_imports, their_exports)) = wasmparser_extern_types(&bytes) else {
            continue;
        };

        let our_imports: Vec<String> = itasca::import_types(&module.env)
            .expect("a validated module resolves every import type")
            .iter()
            .map(ours)
            .collect();
        let our_exports: Vec<String> = itasca::export_types(&module.env)
            .expect("a validated module resolves every export type")
            .iter()
            .map(ours)
            .collect();

        if our_imports != their_imports {
            mismatches.push(format!(
                "{name}: imports {our_imports:?}, wasmparser {their_imports:?}"
            ));
        }
        if our_exports != their_exports {
            mismatches.push(format!(
                "{name}: exports {our_exports:?}, wasmparser {their_exports:?}"
            ));
        }
        if !their_imports.is_empty() {
            with_imports += 1;
        }
        if !their_exports.is_empty() {
            with_exports += 1;
        }
    }

    for m in &mismatches {
        eprintln!("  {m}");
    }
    assert!(
        mismatches.is_empty(),
        "{} extern-type mismatches out of {} files",
        mismatches.len(),
        files.len(),
    );
    assert!(
        with_imports > 0 && with_exports > 0,
        "vacuous: {with_imports} files with imports, {with_exports} with exports"
    );
}
