//! Core 2.0 boundaries that cross instruction, module, and binary decoding rules.
//! The oracle and itasca gates run together for the complete Wasm2 profile.

struct Case {
    name: &'static str,
    bytes: Vec<u8>,
    valid: bool,
}

fn wat(source: &str) -> Vec<u8> {
    let buf = wast::parser::ParseBuffer::new(source).unwrap();
    wast::parser::parse::<wast::Wat>(&buf)
        .unwrap()
        .encode()
        .unwrap()
}

fn leb(mut value: usize, bytes: &mut Vec<u8>) {
    loop {
        let byte = (value % 128) as u8;
        value /= 128;
        bytes.push(byte + if value != 0 { 128 } else { 0 });
        if value == 0 {
            return;
        }
    }
}

fn section(id: u8, contents: &[u8], bytes: &mut Vec<u8>) {
    bytes.push(id);
    leb(contents.len(), bytes);
    bytes.extend(contents);
}

/// A single-function module, preserving instruction bytes verbatim even when
/// their immediates are malformed or nonminimal.
fn body(params: &[u8], results: &[u8], instructions: &[u8]) -> Vec<u8> {
    let mut bytes = b"\0asm\x01\0\0\0".to_vec();
    let mut ty = vec![1, 0x60];
    leb(params.len(), &mut ty);
    ty.extend(params);
    leb(results.len(), &mut ty);
    ty.extend(results);
    section(1, &ty, &mut bytes);
    section(3, &[1, 0], &mut bytes);
    let mut entry = vec![0]; // No locals.
    entry.extend(instructions);
    entry.push(0x0b);
    let mut code = vec![1];
    leb(entry.len(), &mut code);
    code.extend(entry);
    section(10, &code, &mut bytes);
    bytes
}

fn read_leb(bytes: &[u8], pos: &mut usize) -> usize {
    let mut value = 0;
    let mut factor = 1;
    loop {
        let byte = bytes[*pos];
        *pos += 1;
        value += usize::from(byte % 128) * factor;
        if byte < 128 {
            return value;
        }
        factor *= 128;
    }
}

fn replace_data_count(bytes: &[u8], count: Option<u8>, after_code: bool) -> Vec<u8> {
    let mut output = bytes[..8].to_vec();
    let mut pos = 8;
    let mut found = false;
    while pos < bytes.len() {
        let id = bytes[pos];
        pos += 1;
        let len = read_leb(bytes, &mut pos);
        let contents = &bytes[pos..pos + len];
        pos += len;
        if id == 12 {
            found = true;
            if !after_code {
                if let Some(count) = count {
                    section(12, &[count], &mut output);
                }
            }
        } else {
            section(id, contents, &mut output);
            if id == 10 && after_code {
                section(12, &[count.unwrap()], &mut output);
            }
        }
    }
    assert!(
        found,
        "fixture must originally contain a data-count section"
    );
    output
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for (name, source, valid) in [
        (
            "body ref.func does not declare a reference",
            "(module (func $f) (func (result funcref) ref.func $f))",
            false,
        ),
        (
            "declarative element declares a reference",
            "(module (func $f) (elem declare func $f) (func (result funcref) ref.func $f))",
            true,
        ),
        (
            "passive element declares a reference",
            "(module (func $f) (elem func $f) (func (result funcref) ref.func $f))",
            true,
        ),
        (
            "global initializer declares a reference",
            "(module (func $f) (global funcref (ref.func $f)) (func (result funcref) ref.func $f))",
            true,
        ),
        (
            "function export declares a reference",
            "(module (func $f (export \"f\")) (func (result funcref) ref.func $f))",
            true,
        ),
        (
            "start function does not declare a reference",
            "(module (func $f) (start $f) (func (result funcref) ref.func $f))",
            false,
        ),
        (
            "typed select accepts references",
            "(module (func (param externref externref i32) (result externref) local.get 0 local.get 1 local.get 2 select (result externref)))",
            true,
        ),
        (
            "untyped select rejects references",
            "(module (func (param externref externref i32) (result externref) local.get 0 local.get 1 local.get 2 select))",
            false,
        ),
        (
            "multiple tables and indexed call_indirect",
            "(module (type (func)) (table 0 externref) (table 0 funcref) (func i32.const 0 call_indirect 1 (type 0)))",
            true,
        ),
        (
            "call_indirect rejects an externref table",
            "(module (type (func)) (table 0 externref) (func i32.const 0 call_indirect (type 0)))",
            false,
        ),
        (
            "Core 2.0 still has at most one memory",
            "(module (memory 0) (memory 0))",
            false,
        ),
        (
            "passive data needs no memory",
            "(module (data \"bytes\"))",
            true,
        ),
        (
            "table.init checks the segment reference type",
            "(module (table 1 externref) (elem func) (func i32.const 0 i32.const 0 i32.const 0 table.init 0))",
            false,
        ),
        (
            "SIMD extract lane upper bound",
            "(module (func (param v128) (result i32) local.get 0 i8x16.extract_lane_s 15))",
            true,
        ),
        (
            "SIMD extract lane out of range",
            "(module (func (param v128) (result i32) local.get 0 i8x16.extract_lane_s 16))",
            false,
        ),
    ] {
        cases.push(Case { name, bytes: wat(source), valid });
    }

    let memory_init = wat(
        "(module (memory 1) (data \"x\") (func i32.const 0 i32.const 0 i32.const 1 memory.init 0))",
    );
    for (name, bytes, valid) in [
        ("matching data-count before code", memory_init.clone(), true),
        (
            "memory.init requires data-count",
            replace_data_count(&memory_init, None, false),
            false,
        ),
        (
            "data-count must match the data section",
            replace_data_count(&memory_init, Some(2), false),
            false,
        ),
        (
            "data-count must precede code",
            replace_data_count(&memory_init, Some(1), true),
            false,
        ),
    ] {
        cases.push(Case { name, bytes, valid });
    }
    for (name, instructions, valid) in [
        (
            "saturating conversion canonical prefix",
            vec![0x20, 0, 0xfc, 0],
            true,
        ),
        (
            "saturating conversion nonminimal prefix",
            vec![0x20, 0, 0xfc, 0x80, 0],
            true,
        ),
        (
            "saturating conversion five-byte prefix",
            vec![0x20, 0, 0xfc, 0x80, 0x80, 0x80, 0x80, 0],
            true,
        ),
        (
            "saturating conversion overlong prefix",
            vec![0x20, 0, 0xfc, 0x80, 0x80, 0x80, 0x80, 0x80, 0],
            false,
        ),
        (
            "saturating conversion overflowing prefix",
            vec![0x20, 0, 0xfc, 0x80, 0x80, 0x80, 0x80, 0x10],
            false,
        ),
        ("reserved misc prefix", vec![0x20, 0, 0xfc, 0x12], false),
    ] {
        cases.push(Case {
            name,
            bytes: body(&[0x7d], &[0x7f], &instructions),
            valid,
        });
    }
    let mut vector = vec![0xfd, 0x8c, 0]; // Nonminimal v128.const subopcode.
    vector.extend([0; 16]);
    cases.push(Case {
        name: "SIMD nonminimal subopcode",
        bytes: body(&[], &[0x7b], &vector),
        valid: true,
    });
    cases.push(Case {
        name: "relaxed SIMD is outside Core 2.0",
        bytes: body(&[], &[], &[0x00, 0xfd, 0x80, 0x02, 0x1a]),
        valid: false,
    });
    cases.push(Case {
        name: "reserved SIMD subopcode",
        bytes: body(&[], &[], &[0x00, 0xfd, 0xff, 0x7f]),
        valid: false,
    });
    cases
}

fn check(check_itasca: bool) {
    let cases = cases();
    assert_eq!(cases.len(), 28);
    for case in cases {
        let reference = wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
            .validate_all(&case.bytes)
            .is_ok();
        assert_eq!(reference, case.valid, "reference: {}", case.name);
        if check_itasca {
            let actual = itasca::validate_module(&case.bytes, itasca::ValidationProfile::Wasm2);
            assert_eq!(actual.is_ok(), case.valid, "{}: {actual:?}", case.name);
        }
    }
}

#[test]
fn wasm2_boundary_fixtures_match_reference() {
    check(false);
}

#[test]
fn wasm2_boundary_validation() {
    check(true);
}

fn block_module(signature: &[u8], has_result: bool, type_count: usize) -> Vec<u8> {
    let mut bytes = b"\0asm\x01\0\0\0".to_vec();
    let mut types = Vec::new();
    leb(type_count, &mut types);
    for _ in 0..type_count {
        types.extend([0x60, 0, 0]);
    }
    section(1, &types, &mut bytes);
    section(3, &[1, 0], &mut bytes);
    let mut entry = vec![0, 0x02]; // No locals, then block.
    entry.extend(signature);
    entry.extend([0x00, 0x0b]); // Unreachable satisfies any block result.
    if has_result {
        entry.push(0x1a);
    }
    entry.push(0x0b);
    let mut code = vec![1];
    leb(entry.len(), &mut code);
    code.extend(entry);
    section(10, &code, &mut bytes);
    bytes
}

fn check_block(bytes: &[u8], valid: bool) {
    let reference = wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
        .validate_all(bytes)
        .is_ok();
    assert_eq!(reference, valid, "reference: {bytes:02x?}");
    let actual = itasca::validate_module(bytes, itasca::ValidationProfile::Wasm2);
    assert_eq!(actual.is_ok(), valid, "{actual:?}: {bytes:02x?}");
}

#[test]
fn wasm2_inline_block_value_tags() {
    for tag in [0x7f, 0x7e, 0x7d, 0x7c, 0x7b, 0x70, 0x6f] {
        let bytes = block_module(&[tag], true, 1);
        check_block(&bytes, true);
        assert_eq!(
            itasca::validate_module(&bytes, itasca::ValidationProfile::Wasm1).is_ok(),
            tag >= 0x7c,
            "Wasm 1.0 block tag {tag:02x}",
        );
    }
}

#[test]
fn wasm2_block_tags_require_literal_encoding() {
    for tag in [0x40, 0x7f, 0x7e, 0x7d, 0x7c, 0x7b, 0x70, 0x6f] {
        for len in 2..=5 {
            let mut padded = vec![tag + 128];
            padded.extend(std::iter::repeat_n(0xff, len - 2));
            padded.push(0x7f);
            check_block(&block_module(&padded, tag != 0x40, 1), false);
        }
    }
}

#[test]
fn wasm2_block_type_indices_accept_nonminimal_s33() {
    for index in [0, 63, 64, 111, 112, 123, 124, 125, 126, 127, 128] {
        let mut encoding = if index < 64 {
            vec![index]
        } else {
            vec![index % 128 + 128, index / 128]
        };
        loop {
            check_block(&block_module(&encoding, false, 129), true);
            if encoding.len() == 5 {
                break;
            }
            *encoding.last_mut().unwrap() += 128;
            encoding.push(0);
        }
    }
}
