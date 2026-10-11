//! Literal SIMD encodings cover every Core 2.0 opcode and immediate class.
use itasca::{validate_module, ValidationProfile};
const I32: u8 = 0x7f;
const I64: u8 = 0x7e;
const F32: u8 = 0x7d;
const F64: u8 = 0x7c;
const V: u8 = 0x7b;

fn leb(mut value: u32) -> Vec<u8> {
    let mut bytes = Vec::new();
    loop {
        let byte = (value % 128) as u8;
        value /= 128;
        bytes.push(if value == 0 { byte } else { byte + 128 });
        if value == 0 {
            return bytes;
        }
    }
}

fn section(bytes: &mut Vec<u8>, id: u8, payload: &[u8]) {
    bytes.push(id);
    bytes.extend(leb(payload.len() as u32));
    bytes.extend(payload);
}

fn module(inputs: &[u8], outputs: &[u8], operation: &[u8], memory: bool) -> Vec<u8> {
    let mut bytes = vec![0, 97, 115, 109, 1, 0, 0, 0];
    let mut signature = vec![1, 96, inputs.len() as u8];
    signature.extend(inputs);
    signature.push(outputs.len() as u8);
    signature.extend(outputs);
    section(&mut bytes, 1, &signature);
    section(&mut bytes, 3, &[1, 0]);
    if memory {
        section(&mut bytes, 5, &[1, 0, 1]);
    }
    let mut body = vec![0];
    for index in 0..inputs.len() {
        body.extend([32, index as u8]);
    }
    body.extend(operation);
    body.push(11);
    let mut code = vec![1];
    code.extend(leb(body.len() as u32));
    code.extend(body);
    section(&mut bytes, 10, &code);
    bytes
}

fn operation(opcode: u32, immediate: &[u8], padded: bool) -> Vec<u8> {
    let mut bytes = vec![0xfd];
    let mut encoded = leb(opcode);
    if padded {
        while encoded.len() < 5 {
            *encoded.last_mut().unwrap() += 128;
            encoded.push(0);
        }
    }
    bytes.extend(encoded);
    bytes.extend(immediate);
    bytes
}

fn compare(bytes: &[u8], valid: bool) {
    let reference = wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::WASM2)
        .validate_all(bytes)
        .is_ok();
    assert_eq!(reference, valid, "oracle disagreement: {bytes:?}");
    let actual = validate_module(bytes, ValidationProfile::Wasm2);
    assert_eq!(actual.is_ok(), valid, "{actual:?}: {bytes:?}");
}

#[test]
fn every_core2_simd_opcode_and_its_operand_types() {
    let rows: &[(&[u32], &[u8], &[u8], &[u8])] = &[
        (
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 92, 93],
            &[I32],
            &[V],
            &[0, 0],
        ),
        (&[11], &[I32, V], &[], &[0, 0]),
        (&[84, 85, 86, 87], &[I32, V], &[V], &[0, 0, 0]),
        (&[88, 89, 90, 91], &[I32, V], &[], &[0, 0, 0]),
        (&[12], &[], &[V], &[0; 16]),
        (
            &[13],
            &[V, V],
            &[V],
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 31],
        ),
        (&[21, 22, 24, 25, 27], &[V], &[I32], &[0]),
        (&[23, 26, 28], &[V, I32], &[V], &[0]),
        (&[29], &[V], &[I64], &[0]),
        (&[30], &[V, I64], &[V], &[0]),
        (&[31], &[V], &[F32], &[0]),
        (&[32], &[V, F32], &[V], &[0]),
        (&[33], &[V], &[F64], &[0]),
        (&[34], &[V, F64], &[V], &[0]),
        (
            &[
                14, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54,
                55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
                76, 78, 79, 80, 81, 101, 102, 110, 111, 112, 113, 114, 115, 118, 119, 120, 121,
                123, 130, 133, 134, 142, 143, 144, 145, 146, 147, 149, 150, 151, 152, 153, 155,
                156, 157, 158, 159, 174, 177, 181, 182, 183, 184, 185, 186, 188, 189, 190, 191,
                206, 209, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 228, 229, 230,
                231, 232, 233, 234, 235, 240, 241, 242, 243, 244, 245, 246, 247,
            ],
            &[V, V],
            &[V],
            &[],
        ),
        (&[15, 16, 17], &[I32], &[V], &[]),
        (&[18], &[I64], &[V], &[]),
        (&[19], &[F32], &[V], &[]),
        (&[20], &[F64], &[V], &[]),
        (
            &[
                77, 94, 95, 96, 97, 98, 103, 104, 105, 106, 116, 117, 122, 124, 125, 126, 127, 128,
                129, 135, 136, 137, 138, 148, 160, 161, 167, 168, 169, 170, 192, 193, 199, 200,
                201, 202, 224, 225, 227, 236, 237, 239, 248, 249, 250, 251, 252, 253, 254, 255,
            ],
            &[V],
            &[V],
            &[],
        ),
        (&[82], &[V, V, V], &[V], &[]),
        (
            &[83, 99, 100, 131, 132, 163, 164, 195, 196],
            &[V],
            &[I32],
            &[],
        ),
        (
            &[107, 108, 109, 139, 140, 141, 171, 172, 173, 203, 204, 205],
            &[V, I32],
            &[V],
            &[],
        ),
    ];
    let mut count = 0;
    for (opcodes, inputs, outputs, immediate) in rows {
        for opcode in *opcodes {
            count += 1;
            for padded in [false, true] {
                let op = operation(*opcode, immediate, padded);
                let bytes = module(inputs, outputs, &op, true);
                compare(&bytes, true);
                assert!(validate_module(&bytes, ValidationProfile::Wasm1).is_err());
                for index in 0..inputs.len() {
                    let mut wrong = inputs.to_vec();
                    wrong[index] = if wrong[index] == I32 { I64 } else { I32 };
                    compare(&module(&wrong, outputs, &op, true), false);
                }
            }
        }
    }
    assert_eq!(count, 236);
}

#[test]
fn simd_lane_and_shuffle_bounds_are_strict() {
    for (extract, replace, ty, count) in [
        (21, 23, I32, 16),
        (24, 26, I32, 8),
        (27, 28, I32, 4),
        (29, 30, I64, 2),
        (31, 32, F32, 4),
        (33, 34, F64, 2),
    ] {
        for (lane, valid) in [(count - 1, true), (count, false), (255, false)] {
            compare(
                &module(&[V], &[ty], &operation(extract, &[lane], false), true),
                valid,
            );
            compare(
                &module(&[V, ty], &[V], &operation(replace, &[lane], false), true),
                valid,
            );
        }
    }
    for (lane, valid) in [(31, true), (32, false), (255, false)] {
        for position in 0..16 {
            let mut lanes = [0; 16];
            lanes[position] = lane;
            compare(
                &module(&[V, V], &[V], &operation(13, &lanes, false), true),
                valid,
            );
        }
    }
    for length in 0..16 {
        compare(
            &module(&[], &[V], &operation(12, &vec![0; length], false), true),
            false,
        );
        compare(
            &module(&[V, V], &[V], &operation(13, &vec![0; length], false), true),
            false,
        );
    }
}

#[test]
fn simd_memory_checks_presence_alignment_and_lane() {
    let rows: &[(u32, u8, u8, bool)] = &[
        (0, 4, 0, false),
        (1, 3, 0, false),
        (2, 3, 0, false),
        (3, 3, 0, false),
        (4, 3, 0, false),
        (5, 3, 0, false),
        (6, 3, 0, false),
        (7, 0, 0, false),
        (8, 1, 0, false),
        (9, 2, 0, false),
        (10, 3, 0, false),
        (11, 4, 0, true),
        (92, 2, 0, false),
        (93, 3, 0, false),
        (84, 0, 16, false),
        (85, 1, 8, false),
        (86, 2, 4, false),
        (87, 3, 2, false),
        (88, 0, 16, true),
        (89, 1, 8, true),
        (90, 2, 4, true),
        (91, 3, 2, true),
    ];
    for &(opcode, align, lanes, store) in rows {
        let inputs = if store || lanes != 0 {
            &[I32, V][..]
        } else {
            &[I32][..]
        };
        let outputs = if store { &[][..] } else { &[V][..] };
        let mut immediate = vec![align, 0];
        if lanes != 0 {
            immediate.push(lanes - 1);
        }
        compare(
            &module(inputs, outputs, &operation(opcode, &immediate, false), true),
            true,
        );
        compare(
            &module(
                inputs,
                outputs,
                &operation(opcode, &immediate, false),
                false,
            ),
            false,
        );
        immediate[0] = align + 1;
        compare(
            &module(inputs, outputs, &operation(opcode, &immediate, false), true),
            false,
        );
        if lanes != 0 {
            immediate[0] = align;
            immediate[2] = lanes;
            compare(
                &module(inputs, outputs, &operation(opcode, &immediate, false), true),
                false,
            );
        }
    }
}

#[test]
fn simd_reserved_relaxed_and_malformed_prefixes_are_rejected() {
    for opcode in [
        154,
        162,
        165,
        166,
        175,
        176,
        178,
        179,
        180,
        187,
        194,
        197,
        198,
        207,
        208,
        210,
        211,
        212,
        226,
        238,
        256,
        257,
        275,
        u32::MAX,
    ] {
        compare(
            &module(&[], &[], &operation(opcode, &[], false), true),
            false,
        );
    }
    for op in [
        &[0xfd][..],
        &[0xfd, 128, 128, 128, 128, 128, 0],
        &[0xfd, 128, 128, 128, 128, 16],
    ] {
        compare(&module(&[], &[], op, true), false);
    }
}
