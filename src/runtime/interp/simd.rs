//! Portable Core 2.0 SIMD. Lane zero occupies the least significant bits.
use super::super::{ExecError, FloatOps, Trap};
use super::float::{
    binary32, binary64, compare_float, promote, quiet32, quiet64, trunc_int, unary32, unary64,
};
use super::int::compare_int;

fn vector(value: u128) -> u128 {
    value
}
fn from_u32(value: u32) -> u128 {
    value as u128
}
fn from_u64(value: u64) -> u128 {
    value as u128
}

fn mask(width: u32) -> u128 {
    (1u128 << width) - 1
}
fn lane(v: u128, width: u32, index: u32) -> u64 {
    ((v >> (width * index)) & mask(width)) as u64
}
fn signed(v: u64, width: u32) -> i64 {
    ((v << (64 - width)) as i64) >> (64 - width)
}
fn put(v: &mut u128, width: u32, index: u32, x: u64) {
    let shift = width * index;
    *v = (*v & !(mask(width) << shift)) | (((x as u128) & mask(width)) << shift);
}
fn splat(x: u64, width: u32) -> u128 {
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        put(&mut result, width, i, x);
        i += 1;
    }
    result
}
fn sat(x: i128, width: u32, is_signed: bool) -> u64 {
    let lo = if is_signed {
        -(1i128 << (width - 1))
    } else {
        0
    };
    let hi = if is_signed {
        (1i128 << (width - 1)) - 1
    } else {
        (1i128 << width) - 1
    };
    if x < lo {
        lo as u64
    } else if x > hi {
        hi as u64
    } else {
        x as u64
    }
}
fn range(memory: &[u8], address: u32, offset: u32, size: usize) -> Result<usize, ExecError> {
    let start = address as u64 + offset as u64;
    if start + size as u64 > memory.len() as u64 {
        Err(ExecError::Trap(Trap::MemoryOutOfBounds))
    } else {
        Ok(start as usize)
    }
}
fn read(memory: &[u8], start: usize, size: usize) -> u128 {
    let mut x = 0;
    let mut i = 0;
    while i < size {
        x |= (memory[start + i] as u128) << (i * 8);
        i += 1;
    }
    x
}
fn write(memory: &mut [u8], start: usize, size: usize, x: u128) {
    let mut i = 0;
    while i < size {
        memory[start + i] = (x >> (i * 8)) as u8;
        i += 1;
    }
}
fn memory_op(
    op: u32,
    offset: u32,
    lane_index: u32,
    x_in: u128,
    y_in: u128,
    memory: &mut [u8],
) -> Result<u128, ExecError> {
    if op == 0x0b {
        let value = y_in;
        let address = x_in as u32;
        let start = range(memory, address, offset, 16)?;
        write(memory, start, 16, value);
        return Ok(0);
    }
    if op >= 0x54 && op <= 0x5b {
        let width = 8 << ((op - 0x54) % 4);
        if lane_index >= 128 / width {
            return Err(ExecError::BadArguments);
        }
        let mut value = y_in;
        let address = x_in as u32;
        let start = range(memory, address, offset, (width / 8) as usize)?;
        if op >= 0x58 {
            write(
                memory,
                start,
                (width / 8) as usize,
                lane(value, width, lane_index) as u128,
            );
        } else {
            put(
                &mut value,
                width,
                lane_index,
                read(memory, start, (width / 8) as usize) as u64,
            );
            return Ok(value);
        }
        return Ok(0);
    }
    let address = x_in as u32;
    let size = match op {
        0 => 16,
        0x1 | 0x2 | 0x3 | 0x4 | 0x5 | 0x6 => 8,
        0x7 | 0x8 | 0x9 | 0xa => 1 << (op - 7),
        0x5c => 4,
        0x5d => 8,
        _ => return Err(ExecError::BadArguments),
    };
    let start = range(memory, address, offset, size)?;
    let value = read(memory, start, size);
    let result = match op {
        0 | 0x5c | 0x5d => value,
        0x1 | 0x2 | 0x3 | 0x4 | 0x5 | 0x6 => {
            let width = 8 << ((op - 1) / 2);
            let mut result = 0;
            let mut i = 0;
            while i < 64 / width {
                let x = lane(value, width, i);
                let extended = if op % 2 == 1 {
                    signed(x, width) as u64
                } else {
                    x
                };
                put(&mut result, width * 2, i, extended);
                i += 1;
            }
            result
        }
        _ => splat(value as u64, 8 << (op - 7)),
    };
    Ok(result)
}

/// Executes a decoded FD opcode over raw source-order operands. `offset` is
/// the memory offset; `lane_index` selects a lane; `bits` contains const/shuffle
/// bytes. Scalar operands/results occupy low bits. Store instructions return zero.
#[inline(always)]
pub(super) fn simd<F: FloatOps>(
    op: u32,
    offset: u32,
    lane_index: u32,
    bits: u128,
    x_in: u128,
    y_in: u128,
    z_in: u128,
    memory: Option<&mut [u8]>,
) -> Result<u128, ExecError> {
    if op <= 0x0b || (op >= 0x54 && op <= 0x5d) {
        return match memory {
            Some(bytes) => memory_op(op, offset, lane_index, x_in, y_in, bytes),
            None => Err(ExecError::BadArguments),
        };
    }
    let result = match op {
        0x0c => vector(bits),
        0x0d | 0x0e => shuffle_lanes(op, bits, x_in, y_in),
        0xf | 0x10 | 0x11 | 0x12 | 0x13 | 0x14 => splat_lanes(op, x_in),
        0x15 | 0x16 | 0x17 | 0x18 | 0x19 | 0x1a | 0x1b | 0x1c | 0x1d | 0x1e | 0x1f | 0x20
        | 0x21 | 0x22 => return access_lane(op, lane_index, x_in, y_in),
        0x23 | 0x24 | 0x25 | 0x26 | 0x27 | 0x28 | 0x29 | 0x2a | 0x2b | 0x2c | 0x2d | 0x2e
        | 0x2f | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 | 0x36 | 0x37 | 0x38 | 0x39 | 0x3a
        | 0x3b | 0x3c | 0x3d | 0x3e | 0x3f | 0x40 | 0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46
        | 0x47 | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0xd6 | 0xd7 | 0xd8 | 0xd9 | 0xda | 0xdb => {
            compare_lanes(op, x_in, y_in)
        }
        0x4d => vector(!x_in),
        0x4e | 0x4f | 0x50 | 0x51 => bitwise_lanes(op, x_in, y_in),
        0x52 => select_bits(x_in, y_in, z_in),
        0x53 => from_u32((x_in != 0) as u32),
        0x5e | 0x5f | 0xf8 | 0xf9 | 0xfa | 0xfb | 0xfc | 0xfd | 0xfe | 0xff => {
            return convert_lanes::<F>(op, x_in);
        }
        0x67 | 0x68 | 0x69 | 0x6a | 0x74 | 0x75 | 0x7a | 0x94 | 0xe0 | 0xe1 | 0xe3 | 0xec
        | 0xed | 0xef => float_unary_lanes::<F>(op, x_in),
        0xe4 | 0xe5 | 0xe6 | 0xe7 | 0xe8 | 0xe9 | 0xea | 0xeb | 0xf0 | 0xf1 | 0xf2 | 0xf3
        | 0xf4 | 0xf5 | 0xf6 | 0xf7 => float_binary_lanes::<F>(op, x_in, y_in),
        0x60 | 0x61 | 0x62 | 0x63 | 0x64 | 0x80 | 0x81 | 0x83 | 0x84 | 0xa0 | 0xa1 | 0xa3
        | 0xa4 | 0xc0 | 0xc1 | 0xc3 | 0xc4 => integer_unary_lanes(op, x_in),
        0x65 | 0x66 | 0x85 | 0x86 => narrow_lanes(op, x_in, y_in),
        0x7c | 0x7d | 0x7e | 0x7f => pairwise_add_lanes(op, x_in),
        0x87 | 0x88 | 0x89 | 0x8a | 0xa7 | 0xa8 | 0xa9 | 0xaa | 0xc7 | 0xc8 | 0xc9 | 0xca
        | 0x9c | 0x9d | 0x9e | 0x9f | 0xbc | 0xbd | 0xbe | 0xbf | 0xdc | 0xdd | 0xde | 0xdf => {
            widen_lanes(op, x_in, y_in)
        }
        0x6b | 0x6c | 0x6d | 0x8b | 0x8c | 0x8d | 0xab | 0xac | 0xad | 0xcb | 0xcc | 0xcd => {
            shift_lanes(op, x_in, y_in)
        }
        0x82 | 0xba => multiply_lanes(op, x_in, y_in),
        0x6e | 0x6f | 0x70 | 0x71 | 0x72 | 0x73 | 0x76 | 0x77 | 0x78 | 0x79 | 0x7b | 0x8e
        | 0x8f | 0x90 | 0x91 | 0x92 | 0x93 | 0x95 | 0x96 | 0x97 | 0x98 | 0x99 | 0x9b | 0xae
        | 0xb1 | 0xb5 | 0xb6 | 0xb7 | 0xb8 | 0xb9 | 0xce | 0xd1 | 0xd5 => {
            integer_binary_lanes(op, x_in, y_in)
        }
        _ => return Err(ExecError::BadArguments),
    };
    Ok(result)
}

#[inline(always)]
fn shuffle_lanes(op: u32, bits: u128, x_in: u128, y_in: u128) -> u128 {
    let y = y_in;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 16 {
        let n = lane(if op == 0x0d { bits } else { y }, 8, i) as u32;
        let v = if n < 16 {
            lane(x, 8, n)
        } else if op == 0x0d && n < 32 {
            lane(y, 8, n - 16)
        } else {
            0
        };
        put(&mut result, 8, i, v);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn splat_lanes(op: u32, x_in: u128) -> u128 {
    let (x, width) = match op {
        0xf | 0x10 | 0x11 => (x_in as u32 as u64, 8 << (op - 0x0f)),
        0x12 => (x_in as u64, 64),
        0x13 => (x_in as u32 as u64, 32),
        _ => (x_in as u64, 64),
    };
    vector(splat(x, width))
}

#[inline(always)]
fn access_lane(op: u32, lane_index: u32, x_in: u128, y_in: u128) -> Result<u128, ExecError> {
    Ok({
        let width = match op {
            0x15 | 0x16 | 0x17 => 8,
            0x18 | 0x19 | 0x1a => 16,
            0x1b | 0x1c | 0x1f | 0x20 => 32,
            _ => 64,
        };
        if lane_index >= 128 / width {
            return Err(ExecError::BadArguments);
        }
        if matches!(op, 0x17 | 0x1a | 0x1c | 0x1e | 0x20 | 0x22) {
            let x = match op {
                0x1e => y_in as u64,
                0x20 => y_in as u32 as u64,
                0x22 => y_in as u64,
                _ => y_in as u32 as u64,
            };
            let mut v = x_in;
            put(&mut v, width, lane_index, x);
            vector(v)
        } else {
            let x = lane(x_in, width, lane_index);
            match op {
                0x15 | 0x18 => from_u32(signed(x, width) as u32),
                0x1d => from_u64(x),
                0x1f => from_u32(x as u32),
                0x21 => from_u64(x),
                _ => from_u32(x as u32),
            }
        }
    })
}

#[inline(always)]
fn compare_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let y = y_in;
    let x = x_in;
    let (width, cmp, float) = match op {
        0x23 | 0x24 | 0x25 | 0x26 | 0x27 | 0x28 | 0x29 | 0x2a | 0x2b | 0x2c => {
            (8, op - 0x23, false)
        }
        0x2d | 0x2e | 0x2f | 0x30 | 0x31 | 0x32 | 0x33 | 0x34 | 0x35 | 0x36 => {
            (16, op - 0x2d, false)
        }
        0x37 | 0x38 | 0x39 | 0x3a | 0x3b | 0x3c | 0x3d | 0x3e | 0x3f | 0x40 => {
            (32, op - 0x37, false)
        }
        0x41 | 0x42 | 0x43 | 0x44 | 0x45 | 0x46 => (32, op - 0x41, true),
        0x47 | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c => (64, op - 0x47, true),
        _ => (
            64,
            match op {
                0xd6 => 0,
                0xd7 => 1,
                0xd8 => 2,
                0xd9 => 4,
                0xda => 6,
                _ => 8,
            },
            false,
        ),
    };
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let b = lane(y, width, i);
        let yes = if float {
            compare_float(cmp as u16, a, b, width)
        } else {
            compare_int(cmp as u16, a, b, width)
        };
        if yes {
            put(&mut result, width, i, u64::MAX);
        }
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn bitwise_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let y = y_in;
    let x = x_in;
    vector(match op {
        0x4e => x & y,
        0x4f => x & !y,
        0x50 => x | y,
        _ => x ^ y,
    })
}

#[inline(always)]
fn select_bits(x_in: u128, y_in: u128, z_in: u128) -> u128 {
    let c = z_in;
    let y = y_in;
    let x = x_in;
    vector((x & c) | (y & !c))
}

#[inline(always)]
fn convert_lanes<F: FloatOps>(op: u32, x_in: u128) -> Result<u128, ExecError> {
    Ok({
        let x = x_in;
        let mut result = 0;
        let mut i = 0;
        let count = if op == 0x5e || op == 0x5f || op >= 0xfc {
            2
        } else {
            4
        };
        while i < count {
            let (width, bits) = match op {
                0x5e => (32, quiet32(F::f32_demote_f64(lane(x, 64, i))) as u64),
                0x5f => (64, promote(lane(x, 32, i) as u32)),
                0xf8 | 0xf9 => (32, trunc_int(lane(x, 32, i), true, 32, op == 0xf8, true)?),
                0xfa => (
                    32,
                    quiet32(F::f32_convert_i32_s(lane(x, 32, i) as i32)) as u64,
                ),
                0xfb => (
                    32,
                    quiet32(F::f32_convert_i32_u(lane(x, 32, i) as u32)) as u64,
                ),
                0xfc | 0xfd => (32, trunc_int(lane(x, 64, i), false, 32, op == 0xfc, true)?),
                0xfe => (64, quiet64(F::f64_convert_i32_s(lane(x, 32, i) as i32))),
                _ => (64, quiet64(F::f64_convert_i32_u(lane(x, 32, i) as u32))),
            };
            put(&mut result, width, i, bits);
            i += 1;
        }
        vector(result)
    })
}

#[inline(always)]
fn float_unary_lanes<F: FloatOps>(op: u32, x_in: u128) -> u128 {
    let (width, unary) = match op {
        0x67 | 0x68 | 0x69 | 0x6a => (32, op - 0x65),
        0x74 => (64, 2),
        0x75 => (64, 3),
        0x7a => (64, 4),
        0x94 => (64, 5),
        0xe0 => (32, 0),
        0xe1 => (32, 1),
        0xe3 => (32, 6),
        0xec => (64, 0),
        0xed => (64, 1),
        _ => (64, 6),
    };
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let b = if width == 32 {
            unary32::<F>(unary as u16, a as u32) as u64
        } else {
            unary64::<F>(unary as u16, a)
        };
        put(&mut result, width, i, b);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn float_binary_lanes<F: FloatOps>(op: u32, x_in: u128, y_in: u128) -> u128 {
    let width = if op < 0xf0 { 32 } else { 64 };
    let bin = if width == 32 { op - 0xe4 } else { op - 0xf0 };
    let y = y_in;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let b = lane(y, width, i);
        let c = if bin >= 6 {
            if if bin == 6 {
                compare_float(2, b, a, width)
            } else {
                compare_float(2, a, b, width)
            } {
                b
            } else {
                a
            }
        } else if width == 32 {
            binary32::<F>(bin as u16, a as u32, b as u32) as u64
        } else {
            binary64::<F>(bin as u16, a, b)
        };
        put(&mut result, width, i, c);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn integer_unary_lanes(op: u32, x_in: u128) -> u128 {
    let width = 8 << ((op - 0x60) / 0x20);
    let action = op % 0x20;
    let x = x_in;
    let mut result = 0;
    let mut all = true;
    let mut signs = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let s = signed(a, width);
        let b = match action {
            0 => {
                if s < 0 {
                    0u64.wrapping_sub(s as u64)
                } else {
                    s as u64
                }
            }
            1 => 0u64.wrapping_sub(a),
            2 => a.count_ones() as u64,
            _ => a,
        };
        put(&mut result, width, i, b);
        all = all && a != 0;
        signs |= ((a >> (width - 1)) as u32) << i;
        i += 1;
    }
    if action == 3 {
        from_u32(all as u32)
    } else if action == 4 {
        from_u32(signs)
    } else {
        vector(result)
    }
}

#[inline(always)]
fn narrow_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let width = if op < 0x80 { 8 } else { 16 };
    let is_signed = op % 2 == 1;
    let y = y_in;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let source = if i < 64 / width { x } else { y };
        let a = signed(lane(source, width * 2, i % (64 / width)), width * 2);
        put(&mut result, width, i, sat(a as i128, width, is_signed));
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn pairwise_add_lanes(op: u32, x_in: u128) -> u128 {
    let width = if op < 0x7e { 8 } else { 16 };
    let is_signed = op % 2 == 0;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 64 / width {
        let a = lane(x, width, 2 * i);
        let b = lane(x, width, 2 * i + 1);
        let sum = if is_signed {
            (signed(a, width) + signed(b, width)) as u64
        } else {
            a + b
        };
        put(&mut result, width * 2, i, sum);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn widen_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let width = 8 << ((op - 0x80) / 0x20);
    let extmul = op % 0x20 >= 0x1c;
    let variant = op % 0x20 - if extmul { 0x1c } else { 7 };
    let high = variant % 2 == 1;
    let is_signed = variant < 2;
    let y = if extmul { y_in } else { 0 };
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 64 / width {
        let index = i + if high { 64 / width } else { 0 };
        let a = lane(x, width, index);
        let b = lane(y, width, index);
        let a = if is_signed {
            signed(a, width) as u64
        } else {
            a
        };
        let b = if is_signed {
            signed(b, width) as u64
        } else {
            b
        };
        let product = if extmul { a.wrapping_mul(b) } else { a };
        put(&mut result, width * 2, i, product);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn shift_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let width = 8 << ((op - 0x60) / 0x20);
    let shift = y_in as u32 % width;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let b = match op % 0x20 {
            0x0b => a << shift,
            0x0c => (signed(a, width) >> shift) as u64,
            _ => a >> shift,
        };
        put(&mut result, width, i, b);
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn multiply_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let y = y_in;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < if op == 0x82 { 8 } else { 4 } {
        if op == 0x82 {
            let a = signed(lane(x, 16, i), 16);
            let b = signed(lane(y, 16, i), 16);
            put(
                &mut result,
                16,
                i,
                sat(((a * b + 0x4000) >> 15) as i128, 16, true),
            );
        } else {
            let a = signed(lane(x, 16, i * 2), 16) * signed(lane(y, 16, i * 2), 16);
            let b = signed(lane(x, 16, i * 2 + 1), 16) * signed(lane(y, 16, i * 2 + 1), 16);
            put(&mut result, 32, i, (a + b) as u64);
        }
        i += 1;
    }
    vector(result)
}

#[inline(always)]
fn integer_binary_lanes(op: u32, x_in: u128, y_in: u128) -> u128 {
    let width = 8 << ((op - 0x60) / 0x20);
    let y = y_in;
    let x = x_in;
    let mut result = 0;
    let mut i = 0;
    while i < 128 / width {
        let a = lane(x, width, i);
        let b = lane(y, width, i);
        let sa = signed(a, width);
        let sb = signed(b, width);
        let c = match op % 0x20 {
            0x0e => a.wrapping_add(b),
            0x0f => sat(sa as i128 + sb as i128, width, true),
            0x10 => sat(a as i128 + b as i128, width, false),
            0x11 => a.wrapping_sub(b),
            0x12 => sat(sa as i128 - sb as i128, width, true),
            0x13 => sat(a as i128 - b as i128, width, false),
            0x15 => a.wrapping_mul(b),
            0x16 => {
                if sa < sb {
                    a
                } else {
                    b
                }
            }
            0x17 => {
                if a < b {
                    a
                } else {
                    b
                }
            }
            0x18 => {
                if sa > sb {
                    a
                } else {
                    b
                }
            }
            0x19 => {
                if a > b {
                    a
                } else {
                    b
                }
            }
            _ => (a + b + 1) / 2,
        };
        put(&mut result, width, i, c);
        i += 1;
    }
    vector(result)
}

#[cfg(all(test, not(charon)))]
mod tests {
    use super::super::super::native::NativeFloat;
    use super::*;
    #[test]
    fn narrow_q15_and_dot_boundaries() {
        assert_eq!(
            simd::<NativeFloat>(0x66, 0, 0, 0, splat(0xffff, 16), splat(300, 16), 0, None),
            Ok(u128::MAX << 64)
        );
        assert_eq!(
            simd::<NativeFloat>(0x82, 0, 0, 0, splat(0x8000, 16), splat(0x8000, 16), 0, None),
            Ok(splat(0x7fff, 16))
        );
        assert_eq!(
            simd::<NativeFloat>(0xba, 0, 0, 0, splat(0x8000, 16), splat(0x8000, 16), 0, None),
            Ok(splat(0x8000_0000, 32))
        );
    }
    #[test]
    fn memory_does_not_wrap_or_partially_store() {
        let mut memory = [0u8; 32];
        assert_eq!(
            simd::<NativeFloat>(
                0x0b,
                1,
                0,
                0,
                u32::MAX as u128,
                u128::MAX,
                0,
                Some(&mut memory)
            ),
            Err(ExecError::Trap(Trap::MemoryOutOfBounds))
        );
        assert_eq!(memory, [0; 32]);
        assert!(simd::<NativeFloat>(0x0b, 0, 0, 0, 24, u128::MAX, 0, Some(&mut memory)).is_err());
        assert_eq!(memory, [0; 32]);
        assert_eq!(
            simd::<NativeFloat>(0x0b, 0, 0, 0, 16, 0x11223344, 0, Some(&mut memory)),
            Ok(0)
        );
        assert_eq!(
            simd::<NativeFloat>(0, 0, 0, 0, 16, 0, 0, Some(&mut memory)),
            Ok(0x11223344)
        );
    }
    #[test]
    fn pseudo_min_preserves_selected_nan_and_zero_bits() {
        let x = splat(0x7f80_0001, 32);
        assert_eq!(simd::<NativeFloat>(0xea, 0, 0, 0, x, 0, 0, None), Ok(x));
        let x = splat(0x8000_0000, 32);
        assert_eq!(simd::<NativeFloat>(0xeb, 0, 0, 0, x, 0, 0, None), Ok(x));
    }
}
