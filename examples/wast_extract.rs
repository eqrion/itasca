//! Extracts Wasm 1.0 binaries from the spec test suite's `.wast` files into
//! `tests/spec/{valid,invalid}`. Run after updating `tests/third_party/wasm-spec`:
//!
//! ```sh
//! cargo run --example wast_extract
//! ```

use anyhow::{anyhow, Context, Result};
use std::path::{Path, PathBuf};
use wast::core::ModuleKind;
use wast::lexer::Lexer;
use wast::parser::ParseBuffer;
use wast::{QuoteWat, Wast, WastDirective, Wat};

#[path = "../tests/support/mvp_binary.rs"]
mod mvp_binary;

const WAST_DIR: &str = "tests/third_party/wasm-spec/test/core";
const VALID_DIR: &str = "tests/spec/valid";
const INVALID_DIR: &str = "tests/spec/invalid";

fn main() -> Result<()> {
    let wast_dir = PathBuf::from(WAST_DIR);
    let valid_dir = PathBuf::from(VALID_DIR);
    let invalid_dir = PathBuf::from(INVALID_DIR);
    clear_dir(&valid_dir)?;
    clear_dir(&invalid_dir)?;

    let mut total_files = 0;
    let mut valid_count = 0;
    let mut invalid_count = 0;

    let mut entries: Vec<_> = std::fs::read_dir(&wast_dir)
        .with_context(|| format!("reading {}", wast_dir.display()))?
        .collect::<Result<_, _>>()?;
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("wast") {
            continue;
        }
        total_files += 1;
        let (valid, invalid) = extract_modules(&path, &valid_dir, &invalid_dir)
            .with_context(|| format!("processing {}", path.display()))?;
        valid_count += valid;
        invalid_count += invalid;
    }

    println!(
        "Processed {total_files} .wast files, extracted {valid_count} valid + {invalid_count} invalid modules"
    );
    Ok(())
}

fn clear_dir(dir: &Path) -> Result<()> {
    if dir.exists() {
        std::fs::remove_dir_all(dir)?;
    }
    std::fs::create_dir_all(dir)?;
    Ok(())
}

fn write_module(bytes: &[u8], stem: &str, count: &mut usize, dir: &Path) -> Result<()> {
    let filename = if *count == 0 {
        format!("{stem}.wasm")
    } else {
        format!("{stem}_{count}.wasm")
    };
    std::fs::write(dir.join(&filename), bytes)?;
    *count += 1;
    Ok(())
}

fn extract_modules(
    wast_path: &Path,
    valid_dir: &Path,
    invalid_dir: &Path,
) -> Result<(usize, usize)> {
    let source = std::fs::read_to_string(wast_path)?;
    let source = strip_legacy_nan_directives(&source);
    let mut lexer = Lexer::new(&source);
    lexer.allow_confusing_unicode(true);
    let buf = ParseBuffer::new_with_lexer(lexer).map_err(|e| anyhow!("{e}"))?;
    let wast = wast::parser::parse::<Wast>(&buf).map_err(|e| anyhow!("{e}"))?;

    let stem = wast_path.file_stem().unwrap().to_str().unwrap();
    let mut valid_count = 0;
    let mut invalid_count = 0;

    for directive in wast.directives {
        match directive {
            WastDirective::Module(module) | WastDirective::ModuleDefinition(module) => {
                if let Ok(bytes) = encode(module) {
                    write_module(&bytes, stem, &mut valid_count, valid_dir)?;
                }
            }
            // `assert_invalid`/`assert_invalid_custom`: bytes decode fine but the
            // type checker rejects them.
            WastDirective::AssertInvalid { module, .. }
            | WastDirective::AssertInvalidCustom { module, .. } => {
                if let Ok(bytes) = encode(module) {
                    write_module(&bytes, stem, &mut invalid_count, invalid_dir)?;
                }
            }
            // `assert_malformed`/`assert_malformed_custom`: rejected during decoding
            // itself. Only the binary-form ones produce bytes here; text-form
            // malformed cases fail to encode (their whole point is that the text
            // doesn't parse) and are silently skipped, same as any other module
            // whose `encode()` fails.
            WastDirective::AssertMalformed { module, .. }
            | WastDirective::AssertMalformedCustom { module, .. } => {
                if let Ok(bytes) = encode(module) {
                    write_module(&bytes, stem, &mut invalid_count, invalid_dir)?;
                }
            }
            _ => {}
        }
    }

    Ok((valid_count, invalid_count))
}

/// Encodes a module and, unless it was written as literal `(module binary
/// ...)` bytes (already in whatever format the test author intended, often
/// deliberately malformed), rewrites its element/data sections into genuine
/// Wasm 1.0 encoding. See `mvp_binary` for why that rewrite is needed.
fn encode(mut module: QuoteWat) -> Result<Vec<u8>> {
    let verbatim = matches!(
        &module,
        QuoteWat::Wat(Wat::Module(m)) if matches!(m.kind, ModuleKind::Binary(_))
    );
    let bytes = module.encode().map_err(|e| anyhow!("{e}"))?;
    if verbatim {
        return Ok(bytes);
    }
    mvp_binary::normalize_to_wasm1(&bytes).map_err(|e| anyhow!("{}", e.0))
}

/// wg-1.0's `.wast` files predate `assert_return`'s `nan:canonical`/`nan:arithmetic`
/// patterns and instead use standalone `assert_return_canonical_nan`/
/// `assert_return_arithmetic_nan` directives, which the `wast` crate no longer
/// parses. They're runtime assertions we don't need anyway (we only extract
/// modules), so drop them as balanced top-level forms before parsing.
///
/// One pass over the whole file, tracking paren depth and skipping line
/// comments (`;; ...`), nested block comments (`(; ... ;)`), and string
/// literals throughout (not just inside a form) so a stray `(` in comment
/// prose can't be mistaken for a top-level form.
fn strip_legacy_nan_directives(source: &str) -> String {
    const LEGACY: [&str; 2] = [
        "assert_return_canonical_nan",
        "assert_return_arithmetic_nan",
    ];

    let bytes = source.as_bytes();
    let mut out = String::with_capacity(source.len());
    let mut copy_from = 0;
    let mut i = 0;
    let mut depth = 0i32;
    let mut form_start = None;
    while i < bytes.len() {
        match bytes[i] {
            b'(' if bytes.get(i + 1) == Some(&b';') => {
                let mut block_depth = 1;
                i += 2;
                while i < bytes.len() && block_depth > 0 {
                    if bytes[i] == b'(' && bytes.get(i + 1) == Some(&b';') {
                        block_depth += 1;
                        i += 2;
                    } else if bytes[i] == b';' && bytes.get(i + 1) == Some(&b')') {
                        block_depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
            }
            b';' if bytes.get(i + 1) == Some(&b';') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                i += 1;
            }
            b'(' => {
                if depth == 0 {
                    form_start = Some(i);
                }
                depth += 1;
                i += 1;
            }
            b')' => {
                depth -= 1;
                i += 1;
                if depth == 0 {
                    if let Some(start) = form_start.take() {
                        let form = source[start..i].trim_start_matches('(').trim_start();
                        if LEGACY.iter().any(|name| form.starts_with(name)) {
                            out.push_str(&source[copy_from..start]);
                            copy_from = i;
                        }
                    }
                }
            }
            _ => i += 1,
        }
    }
    out.push_str(&source[copy_from..]);
    out
}

#[cfg(test)]
mod strip_tests {
    use super::strip_legacy_nan_directives;

    #[test]
    fn strips_legacy_forms() {
        let src = "(module)\n(assert_return_canonical_nan (invoke \"add\" (f32.const -0x0p+0) (f32.const -nan)))\n(module)\n";
        let out = strip_legacy_nan_directives(src);
        assert!(!out.contains("assert_return_canonical_nan"), "{out}");
    }

    #[test]
    fn parens_in_comments_do_not_confuse_depth_tracking() {
        let src = ";; a comment (with an unbalanced paren\n(module)\n(assert_return_arithmetic_nan (invoke \"f\" (f32.const nan)))\n(module)\n";
        let out = strip_legacy_nan_directives(src);
        assert!(!out.contains("assert_return_arithmetic_nan"), "{out}");
        assert_eq!(out.matches("(module)").count(), 2, "{out}");
    }
}
