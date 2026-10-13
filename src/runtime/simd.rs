//! Portable Core 2.0 SIMD. Lane zero occupies the least significant bits.
use super::*;

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
fn range(memory: &[u8], address: u32, offset: u32, size: usize) -> Result<usize, RuntimeError> {
    let start = address as u64 + offset as u64;
    if start + size as u64 > memory.len() as u64 {
        Err(RuntimeError::Trap(Trap::MemoryOutOfBounds))
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
    stack: &mut Vec<Value>,
    memory: &mut [u8],
) -> Result<(), RuntimeError> {
    if op == 0x0b {
        let value = v128_pop(stack)?;
        let address = i32_pop(stack)?;
        let start = range(memory, address, offset, 16)?;
        write(memory, start, 16, value);
        return Ok(());
    }
    if (0x54..=0x5b).contains(&op) {
        let width = 8 << ((op - 0x54) % 4);
        if lane_index >= 128 / width {
            return Err(RuntimeError::InvalidState);
        }
        let mut value = v128_pop(stack)?;
        let address = i32_pop(stack)?;
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
            stack.push(Value::V128(value));
        }
        return Ok(());
    }
    let address = i32_pop(stack)?;
    let size = match op {
        0 => 16,
        1..=6 => 8,
        7..=10 => 1 << (op - 7),
        0x5c => 4,
        0x5d => 8,
        _ => return Err(RuntimeError::InvalidState),
    };
    let start = range(memory, address, offset, size)?;
    let value = read(memory, start, size);
    let result = match op {
        0 | 0x5c | 0x5d => value,
        1..=6 => {
            let width = 8 << ((op - 1) / 2);
            let mut result = 0;
            let mut i = 0;
            while i < 64 / width {
                let x = lane(value, width, i);
                put(
                    &mut result,
                    width * 2,
                    i,
                    if op % 2 == 1 {
                        signed(x, width) as u64
                    } else {
                        x
                    },
                );
                i += 1;
            }
            result
        }
        _ => splat(value as u64, 8 << (op - 7)),
    };
    stack.push(Value::V128(result));
    Ok(())
}

/// Executes a decoded FD opcode. `a` is offset for memory or lane for lane ops;
/// `bits` contains const/shuffle bytes or a memory-lane index. Alignment is a
/// validated encoding promise and does not change portable memory semantics.
pub(in super::super) fn simd(
    op: u32,
    a: u32,
    _b: u32,
    bits: u128,
    stack: &mut Vec<Value>,
    memory: Option<&mut Vec<u8>>,
) -> Result<(), RuntimeError> {
    if op <= 0x0b || (0x54..=0x5d).contains(&op) {
        return memory_op(
            op,
            a,
            bits as u32,
            stack,
            memory.ok_or(RuntimeError::InvalidState)?,
        );
    }
    let result = match op {
        0x0c => Value::V128(bits),
        0x0d | 0x0e => {
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
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
            Value::V128(result)
        }
        0x0f..=0x14 => {
            let (x, width) = match op {
                0x0f..=0x11 => (i32_pop(stack)? as u64, 8 << (op - 0x0f)),
                0x12 => (i64_pop(stack)?, 64),
                0x13 => (f32_pop(stack)? as u64, 32),
                _ => (f64_pop(stack)?, 64),
            };
            Value::V128(splat(x, width))
        }
        0x15..=0x22 => {
            let width = match op {
                0x15..=0x17 => 8,
                0x18..=0x1a => 16,
                0x1b..=0x1c | 0x1f..=0x20 => 32,
                _ => 64,
            };
            if a >= 128 / width {
                return Err(RuntimeError::InvalidState);
            }
            if matches!(op, 0x17 | 0x1a | 0x1c | 0x1e | 0x20 | 0x22) {
                let x = match op {
                    0x1e => i64_pop(stack)?,
                    0x20 => f32_pop(stack)? as u64,
                    0x22 => f64_pop(stack)?,
                    _ => i32_pop(stack)? as u64,
                };
                let mut v = v128_pop(stack)?;
                put(&mut v, width, a, x);
                Value::V128(v)
            } else {
                let x = lane(v128_pop(stack)?, width, a);
                match op {
                    0x15 | 0x18 => Value::I32(signed(x, width) as u32),
                    0x1d => Value::I64(x),
                    0x1f => Value::F32(x as u32),
                    0x21 => Value::F64(x),
                    _ => Value::I32(x as u32),
                }
            }
        }
        0x23..=0x4c | 0xd6..=0xdb => {
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
            let (width, cmp, float) = match op {
                0x23..=0x2c => (8, op - 0x23, false),
                0x2d..=0x36 => (16, op - 0x2d, false),
                0x37..=0x40 => (32, op - 0x37, false),
                0x41..=0x46 => (32, op - 0x41, true),
                0x47..=0x4c => (64, op - 0x47, true),
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
                    let a = if width == 32 {
                        f32::from_bits(a as u32) as f64
                    } else {
                        f64::from_bits(a)
                    };
                    let b = if width == 32 {
                        f32::from_bits(b as u32) as f64
                    } else {
                        f64::from_bits(b)
                    };
                    compare_float(cmp as u16, a, b)
                } else {
                    compare_int(cmp as u16, a, b, width)
                };
                if yes {
                    put(&mut result, width, i, u64::MAX);
                }
                i += 1;
            }
            Value::V128(result)
        }
        0x4d => Value::V128(!v128_pop(stack)?),
        0x4e..=0x51 => {
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
            Value::V128(match op {
                0x4e => x & y,
                0x4f => x & !y,
                0x50 => x | y,
                _ => x ^ y,
            })
        }
        0x52 => {
            let c = v128_pop(stack)?;
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
            Value::V128((x & c) | (y & !c))
        }
        0x53 => Value::I32((v128_pop(stack)? != 0) as u32),
        0x5e | 0x5f | 0xf8..=0xff => {
            let x = v128_pop(stack)?;
            let mut result = 0;
            let mut i = 0;
            let count = if op == 0x5e || op == 0x5f || op >= 0xfc {
                2
            } else {
                4
            };
            while i < count {
                let (width, bits) = match op {
                    0x5e => (32, quiet32(f64::from_bits(lane(x, 64, i)) as f32) as u64),
                    0x5f => (64, quiet64(f32::from_bits(lane(x, 32, i) as u32) as f64)),
                    0xf8 | 0xf9 => (
                        32,
                        trunc_int(
                            f32::from_bits(lane(x, 32, i) as u32) as f64,
                            32,
                            op == 0xf8,
                            true,
                        )?,
                    ),
                    0xfa => (32, (lane(x, 32, i) as i32 as f32).to_bits() as u64),
                    0xfb => (32, (lane(x, 32, i) as u32 as f32).to_bits() as u64),
                    0xfc | 0xfd => (
                        32,
                        trunc_int(f64::from_bits(lane(x, 64, i)), 32, op == 0xfc, true)?,
                    ),
                    0xfe => (64, (lane(x, 32, i) as i32 as f64).to_bits()),
                    _ => (64, (lane(x, 32, i) as u32 as f64).to_bits()),
                };
                put(&mut result, width, i, bits);
                i += 1;
            }
            Value::V128(result)
        }
        0x67..=0x6a | 0x74 | 0x75 | 0x7a | 0x94 | 0xe0 | 0xe1 | 0xe3 | 0xec | 0xed | 0xef => {
            let (width, unary) = match op {
                0x67..=0x6a => (32, op - 0x65),
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
            let x = v128_pop(stack)?;
            let mut result = 0;
            let mut i = 0;
            while i < 128 / width {
                let a = lane(x, width, i);
                let b = if width == 32 {
                    unary32(unary as u16, a as u32) as u64
                } else {
                    unary64(unary as u16, a)
                };
                put(&mut result, width, i, b);
                i += 1;
            }
            Value::V128(result)
        }
        0xe4..=0xeb | 0xf0..=0xf7 => {
            let width = if op < 0xf0 { 32 } else { 64 };
            let bin = if width == 32 { op - 0xe4 } else { op - 0xf0 };
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
            let mut result = 0;
            let mut i = 0;
            while i < 128 / width {
                let a = lane(x, width, i);
                let b = lane(y, width, i);
                let c = if bin >= 6 {
                    let p = if width == 32 {
                        f32::from_bits(a as u32) as f64
                    } else {
                        f64::from_bits(a)
                    };
                    let q = if width == 32 {
                        f32::from_bits(b as u32) as f64
                    } else {
                        f64::from_bits(b)
                    };
                    if if bin == 6 { q < p } else { p < q } {
                        b
                    } else {
                        a
                    }
                } else if width == 32 {
                    binary32(bin as u16, a as u32, b as u32) as u64
                } else {
                    binary64(bin as u16, a, b)
                };
                put(&mut result, width, i, c);
                i += 1;
            }
            Value::V128(result)
        }
        0x60..=0x64
        | 0x80
        | 0x81
        | 0x83
        | 0x84
        | 0xa0
        | 0xa1
        | 0xa3
        | 0xa4
        | 0xc0
        | 0xc1
        | 0xc3
        | 0xc4 => {
            let width = 8 << ((op - 0x60) / 0x20);
            let action = op % 0x20;
            let x = v128_pop(stack)?;
            let mut result = 0;
            let mut all = true;
            let mut signs = 0;
            let mut i = 0;
            while i < 128 / width {
                let a = lane(x, width, i);
                let s = signed(a, width);
                let b = match action {
                    0 => s.wrapping_abs() as u64,
                    1 => a.wrapping_neg(),
                    2 => a.count_ones() as u64,
                    _ => a,
                };
                put(&mut result, width, i, b);
                all = all && a != 0;
                signs |= ((a >> (width - 1)) as u32) << i;
                i += 1;
            }
            if action == 3 {
                Value::I32(all as u32)
            } else if action == 4 {
                Value::I32(signs)
            } else {
                Value::V128(result)
            }
        }
        0x65 | 0x66 | 0x85 | 0x86 => {
            let width = if op < 0x80 { 8 } else { 16 };
            let is_signed = op % 2 == 1;
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
            let mut result = 0;
            let mut i = 0;
            while i < 128 / width {
                let source = if i < 64 / width { x } else { y };
                let a = signed(lane(source, width * 2, i % (64 / width)), width * 2);
                put(&mut result, width, i, sat(a as i128, width, is_signed));
                i += 1;
            }
            Value::V128(result)
        }
        0x7c..=0x7f => {
            let width = if op < 0x7e { 8 } else { 16 };
            let is_signed = op % 2 == 0;
            let x = v128_pop(stack)?;
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
            Value::V128(result)
        }
        0x87..=0x8a | 0xa7..=0xaa | 0xc7..=0xca | 0x9c..=0x9f | 0xbc..=0xbf | 0xdc..=0xdf => {
            let width = 8 << ((op - 0x80) / 0x20);
            let extmul = op % 0x20 >= 0x1c;
            let variant = op % 0x20 - if extmul { 0x1c } else { 7 };
            let high = variant % 2 == 1;
            let is_signed = variant < 2;
            let y = if extmul { v128_pop(stack)? } else { 0 };
            let x = v128_pop(stack)?;
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
                put(
                    &mut result,
                    width * 2,
                    i,
                    if extmul { a.wrapping_mul(b) } else { a },
                );
                i += 1;
            }
            Value::V128(result)
        }
        0x6b..=0x6d | 0x8b..=0x8d | 0xab..=0xad | 0xcb..=0xcd => {
            let width = 8 << ((op - 0x60) / 0x20);
            let shift = i32_pop(stack)? % width;
            let x = v128_pop(stack)?;
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
            Value::V128(result)
        }
        0x82 | 0xba => {
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
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
            Value::V128(result)
        }
        0x6e..=0x73
        | 0x76..=0x79
        | 0x7b
        | 0x8e..=0x93
        | 0x95..=0x99
        | 0x9b
        | 0xae
        | 0xb1
        | 0xb5..=0xb9
        | 0xce
        | 0xd1
        | 0xd5 => {
            let width = 8 << ((op - 0x60) / 0x20);
            let y = v128_pop(stack)?;
            let x = v128_pop(stack)?;
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
            Value::V128(result)
        }
        _ => return Err(RuntimeError::InvalidState),
    };
    stack.push(result);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    #[test]
    fn narrow_unsigned_treats_source_as_signed() {
        let mut stack = vec![Value::V128(splat(0xffff, 16)), Value::V128(splat(300, 16))];
        simd(0x66, 0, 0, 0, &mut stack, None).unwrap();
        assert_eq!(stack, vec![Value::V128(u128::MAX << 64)]);
    }
    #[test]
    fn q15_corner_and_dot_overflow() {
        let mut stack = vec![
            Value::V128(splat(0x8000, 16)),
            Value::V128(splat(0x8000, 16)),
        ];
        simd(0x82, 0, 0, 0, &mut stack, None).unwrap();
        assert_eq!(stack, vec![Value::V128(splat(0x7fff, 16))]);
        let mut stack = vec![
            Value::V128(splat(0x8000, 16)),
            Value::V128(splat(0x8000, 16)),
        ];
        simd(0xba, 0, 0, 0, &mut stack, None).unwrap();
        assert_eq!(stack, vec![Value::V128(splat(0x8000_0000, 32))]);
    }
    #[test]
    fn memory_does_not_wrap_or_partially_store() {
        let mut memory = vec![0u8; 32];
        let mut stack = vec![Value::I32(u32::MAX), Value::V128(u128::MAX)];
        assert_eq!(
            simd(0x0b, 1, 0, 0, &mut stack, Some(&mut memory)),
            Err(RuntimeError::Trap(Trap::MemoryOutOfBounds))
        );
        assert_eq!(memory, vec![0u8; 32]);
        let mut stack = vec![Value::I32(24), Value::V128(u128::MAX)];
        assert!(simd(0x0b, 0, 0, 0, &mut stack, Some(&mut memory)).is_err());
        assert_eq!(memory, vec![0u8; 32]);
    }
    #[test]
    fn pseudo_min_selects_first_nan_and_signed_zero() {
        let x = splat(0x7f80_0001, 32);
        let mut stack = vec![Value::V128(x), Value::V128(0)];
        simd(0xea, 0, 0, 0, &mut stack, None).unwrap();
        assert_eq!(stack, vec![Value::V128(x)]);
        let x = splat(0x8000_0000, 32);
        let mut stack = vec![Value::V128(x), Value::V128(0)];
        simd(0xeb, 0, 0, 0, &mut stack, None).unwrap();
        assert_eq!(stack, vec![Value::V128(x)]);
    }
}
