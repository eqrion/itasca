//! Scalar integer operations over untagged operand slots.
use super::super::{ExecError, FloatOps, Trap};
use super::float;

pub(super) fn compare_int(op: u16, x: u64, y: u64, width: u32) -> bool {
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

/// Executes any scalar numeric opcode, using the tags from `operators`.
///
/// Integer operators are handled here and the rest are delegated to
/// `float::scalar`. Operands follow Wasm source order and i32 results have
/// zero upper bits.
#[inline(always)]
pub(super) fn scalar<F: FloatOps>(opcode: u16, a: u64, b: u64) -> Result<u64, ExecError> {
    let x = a as u32;
    let y = b as u32;
    let result = match opcode {
        0x45 => (x == 0) as u64,
        0x46 | 0x47 | 0x48 | 0x49 | 0x4a | 0x4b | 0x4c | 0x4d | 0x4e | 0x4f => {
            compare_int(opcode - 0x46, x as u64, y as u64, 32) as u64
        }
        0x50 => (a == 0) as u64,
        0x51 | 0x52 | 0x53 | 0x54 | 0x55 | 0x56 | 0x57 | 0x58 | 0x59 | 0x5a => {
            compare_int(opcode - 0x51, a, b, 64) as u64
        }
        0x67 => x.leading_zeros() as u64,
        0x68 => x.trailing_zeros() as u64,
        0x69 => x.count_ones() as u64,
        0x6a => x.wrapping_add(y) as u64,
        0x6b => x.wrapping_sub(y) as u64,
        0x6c => x.wrapping_mul(y) as u64,
        0x6d | 0x6e | 0x6f | 0x70 => {
            if y == 0 {
                return Err(ExecError::Trap(Trap::IntegerDivideByZero));
            }
            if opcode == 0x6d && x == 0x8000_0000 && y == u32::MAX {
                return Err(ExecError::Trap(Trap::IntegerOverflow));
            }
            (match opcode {
                0x6d => ((x as i32) / (y as i32)) as u32,
                0x6e => x / y,
                0x6f => {
                    if x == 0x8000_0000 && y == u32::MAX {
                        0
                    } else {
                        ((x as i32) % (y as i32)) as u32
                    }
                }
                _ => x % y,
            }) as u64
        }
        0x71 => (x & y) as u64,
        0x72 => (x | y) as u64,
        0x73 => (x ^ y) as u64,
        0x74 => x.wrapping_shl(y) as u64,
        0x75 => (x as i32).wrapping_shr(y) as u32 as u64,
        0x76 => x.wrapping_shr(y) as u64,
        0x77 => x.rotate_left(y) as u64,
        0x78 => x.rotate_right(y) as u64,
        0x79 => a.leading_zeros() as u64,
        0x7a => a.trailing_zeros() as u64,
        0x7b => a.count_ones() as u64,
        0x7c => a.wrapping_add(b),
        0x7d => a.wrapping_sub(b),
        0x7e => a.wrapping_mul(b),
        0x7f | 0x80 | 0x81 | 0x82 => {
            if b == 0 {
                return Err(ExecError::Trap(Trap::IntegerDivideByZero));
            }
            if opcode == 0x7f && a == 0x8000_0000_0000_0000 && b == u64::MAX {
                return Err(ExecError::Trap(Trap::IntegerOverflow));
            }
            match opcode {
                0x7f => ((a as i64) / (b as i64)) as u64,
                0x80 => a / b,
                0x81 => {
                    if a == 0x8000_0000_0000_0000 && b == u64::MAX {
                        0
                    } else {
                        ((a as i64) % (b as i64)) as u64
                    }
                }
                _ => a % b,
            }
        }
        0x83 => a & b,
        0x84 => a | b,
        0x85 => a ^ b,
        0x86 => a.wrapping_shl(b as u32),
        0x87 => (a as i64).wrapping_shr(b as u32) as u64,
        0x88 => a.wrapping_shr(b as u32),
        0x89 => a.rotate_left(b as u32),
        0x8a => a.rotate_right(b as u32),
        0xa7 => x as u64,
        0xac => x as i32 as i64 as u64,
        0xad => x as u64,
        0xc0 => x as i8 as i32 as u32 as u64,
        0xc1 => x as i16 as i32 as u32 as u64,
        0xc2 => a as i8 as i64 as u64,
        0xc3 => a as i16 as i64 as u64,
        0xc4 => a as i32 as i64 as u64,
        _ => return float::scalar::<F>(opcode, a, b),
    };
    Ok(result)
}

#[cfg(all(test, not(charon)))]
mod tests {
    use super::super::super::native::NativeFloat;
    use super::*;
    #[test]
    fn division_traps_and_remainder_wraps() {
        assert_eq!(
            scalar::<NativeFloat>(0x6d, 0x8000_0000, u32::MAX as u64),
            Err(ExecError::Trap(Trap::IntegerOverflow))
        );
        assert_eq!(
            scalar::<NativeFloat>(0x6f, 0x8000_0000, u32::MAX as u64),
            Ok(0)
        );
        assert_eq!(
            scalar::<NativeFloat>(0x7f, 0x8000_0000_0000_0000, u64::MAX),
            Err(ExecError::Trap(Trap::IntegerOverflow))
        );
        assert_eq!(
            scalar::<NativeFloat>(0x81, 0x8000_0000_0000_0000, u64::MAX),
            Ok(0)
        );
        assert_eq!(
            scalar::<NativeFloat>(0x80, 1, 0),
            Err(ExecError::Trap(Trap::IntegerDivideByZero))
        );
    }
    #[test]
    fn shifts_mask_counts_and_zero_upper_i32_bits() {
        assert_eq!(scalar::<NativeFloat>(0x74, 0x8000_0001, 33), Ok(2));
        assert_eq!(
            scalar::<NativeFloat>(0x75, 0x8000_0000, 33),
            Ok(0xc000_0000)
        );
        assert_eq!(
            scalar::<NativeFloat>(0x8a, 1, 65),
            Ok(0x8000_0000_0000_0000)
        );
    }
}
