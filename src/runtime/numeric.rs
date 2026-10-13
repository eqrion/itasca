//! Bit-oriented execution primitives, outside the audited validator model.
//!
//! Floating arithmetic uses the target's IEEE operations; libm supplies no_std
//! rounding and square root. See docs/EXECUTION_NUMERICS.md for the boundary.
use super::{RuntimeError, Trap, Value};
use alloc::vec::Vec;

#[path = "simd.rs"]
mod vector;
pub(super) use vector::simd;

fn pop(stack: &mut Vec<Value>) -> Result<Value, RuntimeError> {
    stack.pop().ok_or(RuntimeError::InvalidState)
}
fn i32_pop(stack: &mut Vec<Value>) -> Result<u32, RuntimeError> {
    match pop(stack)? {
        Value::I32(x) => Ok(x),
        _ => Err(RuntimeError::TypeMismatch),
    }
}
fn i64_pop(stack: &mut Vec<Value>) -> Result<u64, RuntimeError> {
    match pop(stack)? {
        Value::I64(x) => Ok(x),
        _ => Err(RuntimeError::TypeMismatch),
    }
}
fn f32_pop(stack: &mut Vec<Value>) -> Result<u32, RuntimeError> {
    match pop(stack)? {
        Value::F32(x) => Ok(x),
        _ => Err(RuntimeError::TypeMismatch),
    }
}
fn f64_pop(stack: &mut Vec<Value>) -> Result<u64, RuntimeError> {
    match pop(stack)? {
        Value::F64(x) => Ok(x),
        _ => Err(RuntimeError::TypeMismatch),
    }
}
fn v128_pop(stack: &mut Vec<Value>) -> Result<u128, RuntimeError> {
    match pop(stack)? {
        Value::V128(x) => Ok(x),
        _ => Err(RuntimeError::TypeMismatch),
    }
}

// Use canonical positive NaNs for arithmetic. Sign-only and bit reinterpretation
// operators preserve payloads, and SIMD pseudo-min/max preserve selected bits.
fn quiet32(x: f32) -> u32 {
    if x.is_nan() {
        0x7fc0_0000
    } else {
        x.to_bits()
    }
}
fn quiet64(x: f64) -> u64 {
    if x.is_nan() {
        0x7ff8_0000_0000_0000
    } else {
        x.to_bits()
    }
}
fn nearest32(x: f32) -> f32 {
    if !x.is_finite() || libm::fabsf(x) >= 8_388_608.0 {
        return x;
    }
    let t = libm::truncf(x);
    let d = libm::fabsf(x - t);
    let r = if d > 0.5 || (d == 0.5 && (t as i32) % 2 != 0) {
        t + if x < 0.0 { -1.0 } else { 1.0 }
    } else {
        t
    };
    f32::from_bits(r.to_bits() | (x.to_bits() & 0x8000_0000))
}
fn nearest64(x: f64) -> f64 {
    if !x.is_finite() || libm::fabs(x) >= 4_503_599_627_370_496.0 {
        return x;
    }
    let t = libm::trunc(x);
    let d = libm::fabs(x - t);
    let r = if d > 0.5 || (d == 0.5 && (t as i64) % 2 != 0) {
        t + if x < 0.0 { -1.0 } else { 1.0 }
    } else {
        t
    };
    f64::from_bits(r.to_bits() | (x.to_bits() & 0x8000_0000_0000_0000))
}
fn unary32(op: u16, bits: u32) -> u32 {
    let x = f32::from_bits(bits);
    match op {
        0 => bits & 0x7fff_ffff,
        1 => bits ^ 0x8000_0000,
        2 => quiet32(libm::ceilf(x)),
        3 => quiet32(libm::floorf(x)),
        4 => quiet32(libm::truncf(x)),
        5 => quiet32(nearest32(x)),
        _ => quiet32(libm::sqrtf(x)),
    }
}
fn unary64(op: u16, bits: u64) -> u64 {
    let x = f64::from_bits(bits);
    match op {
        0 => bits & 0x7fff_ffff_ffff_ffff,
        1 => bits ^ 0x8000_0000_0000_0000,
        2 => quiet64(libm::ceil(x)),
        3 => quiet64(libm::floor(x)),
        4 => quiet64(libm::trunc(x)),
        5 => quiet64(nearest64(x)),
        _ => quiet64(libm::sqrt(x)),
    }
}
fn binary32(op: u16, a: u32, b: u32) -> u32 {
    let x = f32::from_bits(a);
    let y = f32::from_bits(b);
    match op {
        0 => quiet32(x + y),
        1 => quiet32(x - y),
        2 => quiet32(x * y),
        3 => quiet32(x / y),
        4 | 5 => {
            if x.is_nan() || y.is_nan() {
                return 0x7fc0_0000;
            }
            if x == y {
                return if op == 4 { a | b } else { a & b };
            }
            if (x < y) == (op == 4) {
                a
            } else {
                b
            }
        }
        _ => (a & 0x7fff_ffff) | (b & 0x8000_0000),
    }
}
fn binary64(op: u16, a: u64, b: u64) -> u64 {
    let x = f64::from_bits(a);
    let y = f64::from_bits(b);
    match op {
        0 => quiet64(x + y),
        1 => quiet64(x - y),
        2 => quiet64(x * y),
        3 => quiet64(x / y),
        4 | 5 => {
            if x.is_nan() || y.is_nan() {
                return 0x7ff8_0000_0000_0000;
            }
            if x == y {
                return if op == 4 { a | b } else { a & b };
            }
            if (x < y) == (op == 4) {
                a
            } else {
                b
            }
        }
        _ => (a & 0x7fff_ffff_ffff_ffff) | (b & 0x8000_0000_0000_0000),
    }
}
fn compare_float(op: u16, x: f64, y: f64) -> bool {
    match op {
        0 => x == y,
        1 => x != y,
        2 => x < y,
        3 => x > y,
        4 => x <= y,
        _ => x >= y,
    }
}
fn compare_int(op: u16, x: u64, y: u64, width: u32) -> bool {
    let sx = ((x << (64 - width)) as i64) >> (64 - width);
    let sy = ((y << (64 - width)) as i64) >> (64 - width);
    match op {
        0 => x == y,
        1 => x != y,
        2 => sx < sy,
        3 => x < y,
        4 => sx > sy,
        5 => x > y,
        6 => sx <= sy,
        7 => x <= y,
        8 => sx >= sy,
        _ => x >= y,
    }
}

// Bounds apply after truncation. In particular (-1, 0) converts to unsigned zero,
// and i32 truncation admits negative fractional inputs above -2147483649.
fn trunc_int(x: f64, width: u32, signed: bool, saturating: bool) -> Result<u64, RuntimeError> {
    if saturating {
        return Ok(match (width, signed) {
            (32, true) => (x as i32) as u32 as u64,
            (32, false) => (x as u32) as u64,
            (_, true) => (x as i64) as u64,
            (_, false) => x as u64,
        });
    }
    if x.is_nan() {
        return Err(RuntimeError::Trap(Trap::InvalidConversionToInteger));
    }
    let t = libm::trunc(x);
    let upper = match (width, signed) {
        (32, true) => 2_147_483_648.0,
        (32, false) => 4_294_967_296.0,
        (_, true) => 9_223_372_036_854_775_808.0,
        (_, false) => 18_446_744_073_709_551_616.0,
    };
    let lower = if signed { -upper } else { 0.0 };
    if t < lower || t >= upper {
        return Err(RuntimeError::Trap(Trap::IntegerOverflow));
    }
    Ok(if signed { (t as i64) as u64 } else { t as u64 })
}

/// Executes one scalar numeric opcode; 0x100..0x107 encode FC trunc_sat 0..7.
pub(super) fn scalar(opcode: u16, stack: &mut Vec<Value>) -> Result<(), RuntimeError> {
    let result = match opcode {
        0x45 => Value::I32((i32_pop(stack)? == 0) as u32),
        0x46..=0x4f => {
            let y = i32_pop(stack)?;
            let x = i32_pop(stack)?;
            Value::I32(compare_int(opcode - 0x46, x as u64, y as u64, 32) as u32)
        }
        0x50 => Value::I32((i64_pop(stack)? == 0) as u32),
        0x51..=0x5a => {
            let y = i64_pop(stack)?;
            let x = i64_pop(stack)?;
            Value::I32(compare_int(opcode - 0x51, x, y, 64) as u32)
        }
        0x5b..=0x60 => {
            let y = f32::from_bits(f32_pop(stack)?);
            let x = f32::from_bits(f32_pop(stack)?);
            Value::I32(compare_float(opcode - 0x5b, x as f64, y as f64) as u32)
        }
        0x61..=0x66 => {
            let y = f64::from_bits(f64_pop(stack)?);
            let x = f64::from_bits(f64_pop(stack)?);
            Value::I32(compare_float(opcode - 0x61, x, y) as u32)
        }
        0x67..=0x69 => {
            let x = i32_pop(stack)?;
            Value::I32(match opcode {
                0x67 => x.leading_zeros(),
                0x68 => x.trailing_zeros(),
                _ => x.count_ones(),
            })
        }
        0x6a..=0x78 => {
            let y = i32_pop(stack)?;
            let x = i32_pop(stack)?;
            if (0x6d..=0x70).contains(&opcode) && y == 0 {
                return Err(RuntimeError::Trap(Trap::IntegerDivideByZero));
            }
            if opcode == 0x6d && x == 0x8000_0000 && y == u32::MAX {
                return Err(RuntimeError::Trap(Trap::IntegerOverflow));
            }
            Value::I32(match opcode {
                0x6a => x.wrapping_add(y),
                0x6b => x.wrapping_sub(y),
                0x6c => x.wrapping_mul(y),
                0x6d => ((x as i32) / (y as i32)) as u32,
                0x6e => x / y,
                0x6f => (x as i32).wrapping_rem(y as i32) as u32,
                0x70 => x % y,
                0x71 => x & y,
                0x72 => x | y,
                0x73 => x ^ y,
                0x74 => x.wrapping_shl(y),
                0x75 => (x as i32).wrapping_shr(y) as u32,
                0x76 => x.wrapping_shr(y),
                0x77 => x.rotate_left(y),
                _ => x.rotate_right(y),
            })
        }
        0x79..=0x7b => {
            let x = i64_pop(stack)?;
            Value::I64(match opcode {
                0x79 => x.leading_zeros(),
                0x7a => x.trailing_zeros(),
                _ => x.count_ones(),
            } as u64)
        }
        0x7c..=0x8a => {
            let y = i64_pop(stack)?;
            let x = i64_pop(stack)?;
            if (0x7f..=0x82).contains(&opcode) && y == 0 {
                return Err(RuntimeError::Trap(Trap::IntegerDivideByZero));
            }
            if opcode == 0x7f && x == 0x8000_0000_0000_0000 && y == u64::MAX {
                return Err(RuntimeError::Trap(Trap::IntegerOverflow));
            }
            Value::I64(match opcode {
                0x7c => x.wrapping_add(y),
                0x7d => x.wrapping_sub(y),
                0x7e => x.wrapping_mul(y),
                0x7f => ((x as i64) / (y as i64)) as u64,
                0x80 => x / y,
                0x81 => (x as i64).wrapping_rem(y as i64) as u64,
                0x82 => x % y,
                0x83 => x & y,
                0x84 => x | y,
                0x85 => x ^ y,
                0x86 => x.wrapping_shl(y as u32),
                0x87 => (x as i64).wrapping_shr(y as u32) as u64,
                0x88 => x.wrapping_shr(y as u32),
                0x89 => x.rotate_left(y as u32),
                _ => x.rotate_right(y as u32),
            })
        }
        0x8b..=0x91 => Value::F32(unary32(opcode - 0x8b, f32_pop(stack)?)),
        0x92..=0x98 => {
            let y = f32_pop(stack)?;
            let x = f32_pop(stack)?;
            Value::F32(binary32(opcode - 0x92, x, y))
        }
        0x99..=0x9f => Value::F64(unary64(opcode - 0x99, f64_pop(stack)?)),
        0xa0..=0xa6 => {
            let y = f64_pop(stack)?;
            let x = f64_pop(stack)?;
            Value::F64(binary64(opcode - 0xa0, x, y))
        }
        0xa7 => Value::I32(i64_pop(stack)? as u32),
        0xa8..=0xab | 0xae..=0xb1 | 0x100..=0x107 => {
            let (op, width, sat) = if opcode >= 0x100 {
                (opcode - 0x100, if opcode < 0x104 { 32 } else { 64 }, true)
            } else if opcode <= 0xab {
                (opcode - 0xa8, 32, false)
            } else {
                (opcode - 0xae, 64, false)
            };
            let x = if op % 4 < 2 {
                f32::from_bits(f32_pop(stack)?) as f64
            } else {
                f64::from_bits(f64_pop(stack)?)
            };
            let n = trunc_int(x, width, op % 2 == 0, sat)?;
            if width == 32 {
                Value::I32(n as u32)
            } else {
                Value::I64(n)
            }
        }
        0xac => Value::I64(i32_pop(stack)? as i32 as i64 as u64),
        0xad => Value::I64(i32_pop(stack)? as u64),
        0xb2 => Value::F32((i32_pop(stack)? as i32 as f32).to_bits()),
        0xb3 => Value::F32((i32_pop(stack)? as f32).to_bits()),
        0xb4 => Value::F32((i64_pop(stack)? as i64 as f32).to_bits()),
        0xb5 => Value::F32((i64_pop(stack)? as f32).to_bits()),
        0xb6 => Value::F32(quiet32(f64::from_bits(f64_pop(stack)?) as f32)),
        0xb7 => Value::F64((i32_pop(stack)? as i32 as f64).to_bits()),
        0xb8 => Value::F64((i32_pop(stack)? as f64).to_bits()),
        0xb9 => Value::F64((i64_pop(stack)? as i64 as f64).to_bits()),
        0xba => Value::F64((i64_pop(stack)? as f64).to_bits()),
        0xbb => Value::F64(quiet64(f32::from_bits(f32_pop(stack)?) as f64)),
        0xbc => Value::I32(f32_pop(stack)?),
        0xbd => Value::I64(f64_pop(stack)?),
        0xbe => Value::F32(i32_pop(stack)?),
        0xbf => Value::F64(i64_pop(stack)?),
        0xc0 => Value::I32(i32_pop(stack)? as i8 as i32 as u32),
        0xc1 => Value::I32(i32_pop(stack)? as i16 as i32 as u32),
        0xc2 => Value::I64(i64_pop(stack)? as i8 as i64 as u64),
        0xc3 => Value::I64(i64_pop(stack)? as i16 as i64 as u64),
        0xc4 => Value::I64(i64_pop(stack)? as i32 as i64 as u64),
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
    fn truncation_checks_truncated_value_and_exclusive_upper_bound() {
        assert_eq!(
            trunc_int(-2147483648.75, 32, true, false),
            Ok(0xffff_ffff_8000_0000)
        );
        assert_eq!(trunc_int(-0.99, 32, false, false), Ok(0));
        assert!(trunc_int(2147483648.0, 32, true, false).is_err());
        assert!(trunc_int(18446744073709551616.0, 64, false, false).is_err());
        assert_eq!(trunc_int(f64::NAN, 64, false, true), Ok(0));
        assert_eq!(trunc_int(f64::INFINITY, 64, false, true), Ok(u64::MAX));
    }
    #[test]
    fn signed_zero_nan_and_ties() {
        assert_eq!(binary32(4, 0, 0x8000_0000), 0x8000_0000);
        assert_eq!(binary32(5, 0x8000_0000, 0), 0);
        assert_eq!(unary32(0, 0xff80_0001), 0x7f80_0001);
        assert_eq!(nearest64(-0.5).to_bits(), (-0.0f64).to_bits());
        assert_eq!(nearest64(2.5), 2.0);
        assert_eq!(nearest64(3.5), 4.0);
    }
    #[test]
    fn division_traps_but_signed_remainder_wraps() {
        let mut s = vec![Value::I32(0x8000_0000), Value::I32(u32::MAX)];
        assert_eq!(
            scalar(0x6d, &mut s),
            Err(RuntimeError::Trap(Trap::IntegerOverflow))
        );
        let mut s = vec![Value::I32(0x8000_0000), Value::I32(u32::MAX)];
        scalar(0x6f, &mut s).unwrap();
        assert_eq!(s, vec![Value::I32(0)]);
    }
}
