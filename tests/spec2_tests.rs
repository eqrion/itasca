//! Pinned wg-2.0 control-flow corpus. No Wasm 1.0 binary normalization.
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
) {
    let bytes = match module.encode() {
        Ok(bytes) => bytes,
        Err(_) if malformed && matches!(module, QuoteWat::QuoteModule(..)) => {
            counts.malformed_text += 1;
            return;
        }
        Err(e) => panic!("{}:{line}: unexpected encoding error: {e}", path.display()),
    };
    let mut features = wasmparser::WasmFeatures::WASM1;
    features.set(wasmparser::WasmFeatures::MULTI_VALUE, true);
    let reference = wasmparser::Validator::new_with_features(features)
        .validate_all(&bytes)
        .is_ok();
    if valid && !reference {
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
    let result = itasca::multi_value::validate_module(&bytes);
    assert_eq!(
        result.is_ok(),
        valid,
        "{}:{line}: {result:?}",
        path.display()
    );
    if valid {
        counts.valid += 1;
    } else {
        counts.invalid += 1;
    }
}

#[test]
fn wasm2_multivalue_corpus() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/spec2");
    let mut files: Vec<_> = std::fs::read_dir(root)
        .unwrap()
        .map(|x| x.unwrap().path())
        .filter(|x| x.extension().is_some_and(|e| e == "wast"))
        .collect();
    files.sort();
    assert_eq!(files.len(), 15);
    let mut counts = Counts::default();
    for path in files {
        let source = std::fs::read_to_string(&path).unwrap();
        let buf = wast::parser::ParseBuffer::new(&source).unwrap();
        let wast = wast::parser::parse::<Wast>(&buf).unwrap();
        for directive in wast.directives {
            let line = directive.span().linecol_in(&source).0 + 1;
            match directive {
                WastDirective::Module(module) | WastDirective::ModuleDefinition(module) => {
                    check_module(module, true, false, &path, line, &mut counts)
                }
                WastDirective::AssertInvalid { module, .. } => {
                    check_module(module, false, false, &path, line, &mut counts)
                }
                WastDirective::AssertMalformed { module, .. } => {
                    check_module(module, false, true, &path, line, &mut counts)
                }
                WastDirective::AssertUnlinkable { module, .. } => {
                    check_module(QuoteWat::Wat(module), true, false, &path, line, &mut counts)
                }
                WastDirective::AssertTrap {
                    exec: WastExecute::Wat(module),
                    ..
                }
                | WastDirective::AssertReturn {
                    exec: WastExecute::Wat(module),
                    ..
                } => check_module(QuoteWat::Wat(module), true, false, &path, line, &mut counts),
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
    assert_eq!(
        counts,
        Counts {
            valid: 17,
            invalid: 489,
            unsupported: 4,
            malformed_text: 90,
            runtime: 1186,
        }
    );
}
