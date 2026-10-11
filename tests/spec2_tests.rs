//! Pinned complete wg-2.0 corpus. No binary normalization or feature exclusions
//! in the full-profile tests; the older control-flow gate remains during migration.
use std::path::{Path, PathBuf};
use wast::{QuoteWat, Wast, WastDirective, WastExecute};

#[derive(Default, Debug, PartialEq, Eq)]
struct Counts {
    valid: usize,
    invalid: usize,
    unsupported: usize,
    malformed_text: usize,
    runtime: usize,
}

fn check_module(
    mut module: QuoteWat<'_>,
    valid: bool,
    malformed: bool,
    path: &Path,
    line: usize,
    counts: &mut Counts,
    control_only: bool,
    check_itasca: bool,
) {
    let bytes = match module.encode() {
        Ok(bytes) => bytes,
        Err(_) if malformed && matches!(module, QuoteWat::QuoteModule(..)) => {
            counts.malformed_text += 1;
            return;
        }
        Err(e) => panic!("{}:{line}: unexpected encoding error: {e}", path.display()),
    };
    let features = if control_only {
        wasmparser::WasmFeatures::WASM1 | wasmparser::WasmFeatures::MULTI_VALUE
    } else {
        wasmparser::WasmFeatures::WASM2
    };
    let reference = wasmparser::Validator::new_with_features(features)
        .validate_all(&bytes)
        .is_ok();
    if control_only && valid && !reference {
        // Classify exclusions independently of itasca. They must still be valid
        // Wasm 2.0, so broken encoding/extraction cannot silently lose coverage.
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
            .validate_all(&bytes)
            .unwrap_or_else(|e| panic!("{}:{line}: invalid positive fixture: {e}", path.display()));
        eprintln!(
            "unsupported {}:{line}",
            path.file_name().unwrap().to_string_lossy()
        );
        counts.unsupported += 1;
        return;
    }
    assert_eq!(
        reference,
        valid,
        "{}:{line}: reference disagrees with WAST assertion",
        path.display()
    );
    if check_itasca {
        let result = itasca::validate_module(&bytes, itasca::ValidationProfile::Wasm2);
        assert_eq!(
            result.is_ok(),
            valid,
            "{}:{line}: {result:?}",
            path.display()
        );
    }
    if valid {
        counts.valid += 1;
    } else {
        counts.invalid += 1;
    }
}

const CONTROL_FILES: &[&str] = &[
    "block.wast",
    "br.wast",
    "br_if.wast",
    "br_table.wast",
    "call.wast",
    "call_indirect.wast",
    "func.wast",
    "if.wast",
    "labels.wast",
    "loop.wast",
    "return.wast",
    "select.wast",
    "type.wast",
    "unreachable.wast",
    "unwind.wast",
];

fn collect_wast(dir: &Path, files: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_wast(&path, files);
        } else if path.extension().is_some_and(|ext| ext == "wast") {
            files.push(path);
        }
    }
}

fn run_corpus(control_only: bool, check_itasca: bool) -> Counts {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/spec2");
    let mut files = Vec::new();
    if control_only {
        files.extend(CONTROL_FILES.iter().map(|name| root.join(name)));
    } else {
        collect_wast(&root, &mut files);
        assert_eq!(files.len(), 148, "pinned complete Core 2.0 WAST count");
        assert_eq!(
            files
                .iter()
                .filter(|p| p.parent().unwrap().ends_with("simd"))
                .count(),
            58
        );
    }
    files.sort();
    let mut counts = Counts::default();
    for path in files {
        let source = std::fs::read_to_string(&path).unwrap();
        let mut lexer = wast::lexer::Lexer::new(&source);
        lexer.allow_confusing_unicode(true);
        let buf = wast::parser::ParseBuffer::new_with_lexer(lexer)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let wast = wast::parser::parse::<Wast>(&buf).unwrap();
        for directive in wast.directives {
            let line = directive.span().linecol_in(&source).0 + 1;
            match directive {
                WastDirective::Module(module) | WastDirective::ModuleDefinition(module) => {
                    check_module(
                        module,
                        true,
                        false,
                        &path,
                        line,
                        &mut counts,
                        control_only,
                        check_itasca,
                    )
                }
                WastDirective::AssertInvalid { module, .. } => check_module(
                    module,
                    false,
                    false,
                    &path,
                    line,
                    &mut counts,
                    control_only,
                    check_itasca,
                ),
                WastDirective::AssertMalformed { module, .. } => check_module(
                    module,
                    false,
                    true,
                    &path,
                    line,
                    &mut counts,
                    control_only,
                    check_itasca,
                ),
                WastDirective::AssertUnlinkable { module, .. } => check_module(
                    QuoteWat::Wat(module),
                    true,
                    false,
                    &path,
                    line,
                    &mut counts,
                    control_only,
                    check_itasca,
                ),
                WastDirective::AssertTrap {
                    exec: WastExecute::Wat(module),
                    ..
                }
                | WastDirective::AssertReturn {
                    exec: WastExecute::Wat(module),
                    ..
                } => check_module(
                    QuoteWat::Wat(module),
                    true,
                    false,
                    &path,
                    line,
                    &mut counts,
                    control_only,
                    check_itasca,
                ),
                WastDirective::Invoke(_)
                | WastDirective::Register { .. }
                | WastDirective::AssertExhaustion { .. }
                | WastDirective::AssertReturn { .. }
                | WastDirective::AssertTrap { .. } => counts.runtime += 1,
                unexpected => panic!(
                    "{}:{line}: unhandled directive {unexpected:?}",
                    path.display()
                ),
            }
        }
    }
    eprintln!("{counts:?}");
    counts
}

#[test]
fn wasm2_multivalue_corpus() {
    assert_eq!(
        run_corpus(true, true),
        Counts {
            valid: 17,
            invalid: 489,
            unsupported: 4,
            malformed_text: 90,
            runtime: 1186,
        }
    );
}

#[test]
fn wasm2_corpus_matches_reference() {
    assert_eq!(run_corpus(false, false), FULL_COUNTS);
}

#[test]
fn wasm2_complete_corpus() {
    assert_eq!(run_corpus(false, true), FULL_COUNTS);
}

const FULL_COUNTS: Counts = Counts {
    valid: 1716,
    invalid: 2875,
    unsupported: 0,
    malformed_text: 1081,
    runtime: 48334,
};
