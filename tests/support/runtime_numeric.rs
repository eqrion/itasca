//! Small, deterministic numeric programs shared by fuzzing and regressions.
//!
//! Each export performs exactly one numeric operation, with no control flow or
//! observable state derived from floating NaN payloads. Arithmetic float inputs
//! are finite and bounded; square-root inputs are nonnegative and divisors are
//! nonzero. Comparisons, trapping/saturating float-to-integer conversions, and
//! exact bit-selection operations receive arbitrary float bits, including NaNs,
//! infinities and subnormals. Integer lanes retain all input bits.
#![allow(dead_code)]
use itasca::ValidationProfile;

const I32: u8 = 0x7f;
const I64: u8 = 0x7e;
const F32: u8 = 0x7d;
const F64: u8 = 0x7c;
const V128: u8 = 0x7b;

fn leb(mut x: u32, out: &mut Vec<u8>) {
    loop {
        let byte = (x % 128) as u8;
        x /= 128;
        out.push(byte | if x == 0 { 0 } else { 0x80 });
        if x == 0 {
            break;
        }
    }
}
fn sleb(mut x: i64, out: &mut Vec<u8>) {
    loop {
        let byte = (x & 127) as u8;
        x >>= 7;
        let done = (x == 0 && byte & 64 == 0) || (x == -1 && byte & 64 != 0);
        out.push(byte | if done { 0 } else { 0x80 });
        if done {
            break;
        }
    }
}
fn byte(data: &[u8], index: usize) -> u8 {
    if data.is_empty() {
        0
    } else {
        data[index % data.len()]
    }
}
fn word(data: &[u8], index: usize) -> u64 {
    let mut x = 0;
    let mut i = 0;
    while i < 8 {
        x |= (byte(data, index + i) as u64) << (8 * i);
        i += 1;
    }
    x
}
fn finite(data: &[u8], index: usize) -> f64 {
    // Nonzero, at most 2^21 in magnitude. Products and quotients stay finite.
    let x = word(data, index) as i32;
    if x == 0 {
        1.0 / 1024.0
    } else {
        x as f64 / 1024.0
    }
}
fn scalar_signature(op: u16) -> (&'static [u8], u8) {
    match op {
        0x45 | 0x67..=0x69 | 0xc0 | 0xc1 => (&[I32], I32),
        0x46..=0x4f | 0x6a..=0x78 => (&[I32, I32], I32),
        0x50 | 0xa7 => (&[I64], I32),
        0x51..=0x5a => (&[I64, I64], I32),
        0x5b..=0x60 => (&[F32, F32], I32),
        0x61..=0x66 => (&[F64, F64], I32),
        0x79..=0x7b | 0xc2..=0xc4 => (&[I64], I64),
        0x7c..=0x8a => (&[I64, I64], I64),
        0x8b..=0x91 => (&[F32], F32),
        0x92..=0x98 => (&[F32, F32], F32),
        0x99..=0x9f => (&[F64], F64),
        0xa0..=0xa6 => (&[F64, F64], F64),
        0xa8..=0xa9 | 0xbc | 0x100..=0x101 => (&[F32], I32),
        0xaa..=0xab | 0x102..=0x103 => (&[F64], I32),
        0xac..=0xad => (&[I32], I64),
        0xae..=0xaf | 0x104..=0x105 => (&[F32], I64),
        0xb0..=0xb1 | 0xbd | 0x106..=0x107 => (&[F64], I64),
        0xb2..=0xb3 | 0xbe => (&[I32], F32),
        0xb4..=0xb5 => (&[I64], F32),
        0xb6 => (&[F64], F32),
        0xb7..=0xb8 => (&[I32], F64),
        0xb9..=0xba | 0xbf => (&[I64], F64),
        0xbb => (&[F32], F64),
        _ => unreachable!(),
    }
}
fn simd_signature(op: u32) -> Option<(&'static [u8], u8)> {
    Some(match op {
        0x0c => (&[], V128),
        0x0f..=0x11 => (&[I32], V128),
        0x12 => (&[I64], V128),
        0x13 => (&[F32], V128),
        0x14 => (&[F64], V128),
        0x15..=0x16
        | 0x18..=0x19
        | 0x1b
        | 0x53
        | 0x63..=0x64
        | 0x83..=0x84
        | 0xa3..=0xa4
        | 0xc3..=0xc4 => (&[V128], I32),
        0x17 | 0x1a | 0x1c | 0x6b..=0x6d | 0x8b..=0x8d | 0xab..=0xad | 0xcb..=0xcd => {
            (&[V128, I32], V128)
        }
        0x1d => (&[V128], I64),
        0x1e => (&[V128, I64], V128),
        0x1f => (&[V128], F32),
        0x20 => (&[V128, F32], V128),
        0x21 => (&[V128], F64),
        0x22 => (&[V128, F64], V128),
        0x52 => (&[V128, V128, V128], V128),
        0x4d
        | 0x5e..=0x62
        | 0x67..=0x6a
        | 0x74..=0x75
        | 0x7a
        | 0x7c..=0x81
        | 0x87..=0x8a
        | 0x94
        | 0xa0..=0xa1
        | 0xa7..=0xaa
        | 0xc0..=0xc1
        | 0xc7..=0xca
        | 0xe0..=0xe1
        | 0xe3
        | 0xec..=0xed
        | 0xef
        | 0xf8..=0xff => (&[V128], V128),
        0x0d..=0x0e
        | 0x23..=0x4c
        | 0x4e..=0x51
        | 0x65..=0x66
        | 0x6e..=0x73
        | 0x76..=0x79
        | 0x7b
        | 0x82
        | 0x85..=0x86
        | 0x8e..=0x93
        | 0x95..=0x99
        | 0x9b..=0x9f
        | 0xae
        | 0xb1
        | 0xb5..=0xba
        | 0xbc..=0xbf
        | 0xce
        | 0xd1
        | 0xd5..=0xdf
        | 0xe4..=0xeb
        | 0xf0..=0xf7 => (&[V128, V128], V128),
        _ => return None,
    })
}
fn float_lanes(op: u32) -> Option<u32> {
    match op {
        0x5f | 0x67..=0x6a | 0xe3..=0xe9 => Some(32),
        0x5e | 0x74..=0x75 | 0x7a | 0x94 | 0xef..=0xf5 => Some(64),
        _ => None,
    }
}
fn constant(
    ty: u8,
    data: &[u8],
    index: usize,
    positive: bool,
    lanes: Option<u32>,
    raw_float: bool,
    out: &mut Vec<u8>,
) {
    match ty {
        I32 => {
            out.push(0x41);
            sleb(word(data, index) as i32 as i64, out);
        }
        I64 => {
            out.push(0x42);
            sleb(word(data, index) as i64, out);
        }
        F32 | F64 => {
            let mut f = finite(data, index);
            if positive && f < 0.0 {
                f = -f;
            }
            if ty == F32 {
                out.push(0x43);
                let bits = if raw_float {
                    word(data, index) as u32
                } else {
                    (f as f32).to_bits()
                };
                out.extend_from_slice(&bits.to_le_bytes());
            } else {
                out.push(0x44);
                let bits = if raw_float {
                    word(data, index)
                } else {
                    f.to_bits()
                };
                out.extend_from_slice(&bits.to_le_bytes());
            }
        }
        V128 => {
            out.extend_from_slice(&[0xfd, 0x0c]);
            let width = lanes.unwrap_or(64);
            let mut i = 0;
            while i < 128 / width {
                let mut f = finite(data, index + i as usize * 4);
                if positive && f < 0.0 {
                    f = -f;
                }
                if lanes == Some(32) {
                    out.extend_from_slice(&(f as f32).to_bits().to_le_bytes());
                } else if lanes == Some(64) {
                    out.extend_from_slice(&f.to_bits().to_le_bytes());
                } else {
                    out.extend_from_slice(&word(data, index + i as usize * 8).to_le_bytes());
                }
                i += 1;
            }
        }
        _ => unreachable!(),
    }
}
fn section(id: u8, payload: &[u8], module: &mut Vec<u8>) {
    module.push(id);
    leb(payload.len() as u32, module);
    module.extend_from_slice(payload);
}

/// Builds a one-operation module. Bytes 0/1 choose profile/opcode, remaining
/// bytes seed constants and lane/shuffle immediates. There are no filtering exits.
pub fn module(data: &[u8]) -> (Vec<u8>, ValidationProfile) {
    let profile = if byte(data, 0) % 3 == 0 {
        ValidationProfile::Wasm1
    } else {
        ValidationProfile::Wasm2
    };
    let is_simd = byte(data, 0) % 3 == 2;
    let mut op = byte(data, 1) as u16;
    let (params, result) = if is_simd {
        loop {
            if let Some(sig) = simd_signature(op as u32) {
                break sig;
            }
            op = (op + 1) % 256;
        }
    } else {
        let count = if matches!(profile, ValidationProfile::Wasm1) {
            123
        } else {
            136
        };
        op %= count;
        op = if op < 128 {
            op + 0x45
        } else {
            op - 128 + 0x100
        };
        scalar_signature(op)
    };
    let mut body = vec![0];
    let mut i = 0;
    while i < params.len() {
        constant(
            params[i],
            data,
            2 + i * 16,
            if is_simd {
                matches!(op, 0xe3 | 0xef)
            } else {
                matches!(op, 0x91 | 0x9f)
            },
            if is_simd {
                float_lanes(op as u32)
            } else {
                None
            },
            !is_simd
                && matches!(op, 0x5b..=0x66 | 0x8b..=0x8c | 0x98..=0x9a | 0xa6 | 0xa8..=0xab | 0xae..=0xb1 | 0xbc..=0xbd | 0x100..=0x107),
            &mut body,
        );
        i += 1;
    }
    if is_simd {
        body.push(0xfd);
        leb(op as u32, &mut body);
        if op == 0x0c || op == 0x0d {
            let mut i = 0;
            while i < 16 {
                body.push(if op == 0x0d {
                    byte(data, 2 + i) % 32
                } else {
                    byte(data, 2 + i)
                });
                i += 1;
            }
        } else if (0x15..=0x22).contains(&op) {
            let count = match op {
                0x15..=0x17 => 16,
                0x18..=0x1a => 8,
                0x1b..=0x1c | 0x1f..=0x20 => 4,
                _ => 2,
            };
            body.push(byte(data, 2) % count);
        }
    } else if op >= 0x100 {
        body.extend_from_slice(&[0xfc, (op - 0x100) as u8]);
    } else {
        body.push(op as u8);
    }
    body.push(0x0b);
    let mut module = b"\0asm\x01\0\0\0".to_vec();
    section(1, &[1, 0x60, 0, 1, result], &mut module);
    section(3, &[1, 0], &mut module);
    section(7, &[1, 3, b'r', b'u', b'n', 0, 0], &mut module);
    let mut code = vec![1];
    leb(body.len() as u32, &mut code);
    code.extend_from_slice(&body);
    section(10, &code, &mut module);
    (module, profile)
}
