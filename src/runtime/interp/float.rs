//! Float bit operations and wrappers around the embedding's IEEE rounding ops.
use super::super::{ExecError, FloatOps, Trap};

pub(super) fn quiet32(bits: u32) -> u32 {
    if bits & 0x7fff_ffff > 0x7f80_0000 {
        0x7fc0_0000
    } else {
        bits
    }
}
pub(super) fn quiet64(bits: u64) -> u64 {
    if bits & 0x7fff_ffff_ffff_ffff > 0x7ff0_0000_0000_0000 {
        0x7ff8_0000_0000_0000
    } else {
        bits
    }
}

/// IEEE comparisons using sign and magnitude bits, including unordered NaNs.
pub(super) fn compare_float(op: u16, a: u64, b: u64, width: u32) -> bool {
    let (sign, infinity) = if width == 32 {
        (0x8000_0000, 0x7f80_0000)
    } else {
        (0x8000_0000_0000_0000, 0x7ff0_0000_0000_0000)
    };
    let ma = a & (sign - 1);
    let mb = b & (sign - 1);
    if ma > infinity || mb > infinity {
        return op == 1;
    }
    let equal = a == b || (ma == 0 && mb == 0);
    let less = !equal && less_float_bits(a, b, sign);
    match op {
        0 => equal,
        1 => !equal,
        2 => less,
        3 => !less && !equal,
        4 => less || equal,
        _ => !less,
    }
}

#[inline(always)]
fn less_float_bits(a: u64, b: u64, sign: u64) -> bool {
    if (a & sign) != (b & sign) {
        a & sign != 0
    } else if a & sign == 0 {
        a < b
    } else {
        a > b
    }
}

pub(super) fn unary32<F: FloatOps>(op: u16, bits: u32) -> u32 {
    match op {
        0 => bits & 0x7fff_ffff,
        1 => bits ^ 0x8000_0000,
        2 => quiet32(F::f32_ceil(bits)),
        3 => quiet32(F::f32_floor(bits)),
        4 => quiet32(F::f32_trunc(bits)),
        5 => quiet32(F::f32_nearest(bits)),
        _ => quiet32(F::f32_sqrt(bits)),
    }
}
pub(super) fn unary64<F: FloatOps>(op: u16, bits: u64) -> u64 {
    match op {
        0 => bits & 0x7fff_ffff_ffff_ffff,
        1 => bits ^ 0x8000_0000_0000_0000,
        2 => quiet64(F::f64_ceil(bits)),
        3 => quiet64(F::f64_floor(bits)),
        4 => quiet64(F::f64_trunc(bits)),
        5 => quiet64(F::f64_nearest(bits)),
        _ => quiet64(F::f64_sqrt(bits)),
    }
}
pub(super) fn binary32<F: FloatOps>(op: u16, a: u32, b: u32) -> u32 {
    match op {
        0 => quiet32(F::f32_add(a, b)),
        1 => quiet32(F::f32_sub(a, b)),
        2 => quiet32(F::f32_mul(a, b)),
        3 => quiet32(F::f32_div(a, b)),
        4 | 5 => {
            if a & 0x7fff_ffff > 0x7f80_0000 || b & 0x7fff_ffff > 0x7f80_0000 {
                return 0x7fc0_0000;
            }
            if compare_float(0, a as u64, b as u64, 32) {
                if op == 4 {
                    a | b
                } else {
                    a & b
                }
            } else if compare_float(2, a as u64, b as u64, 32) == (op == 4) {
                a
            } else {
                b
            }
        }
        _ => (a & 0x7fff_ffff) | (b & 0x8000_0000),
    }
}
pub(super) fn binary64<F: FloatOps>(op: u16, a: u64, b: u64) -> u64 {
    match op {
        0 => quiet64(F::f64_add(a, b)),
        1 => quiet64(F::f64_sub(a, b)),
        2 => quiet64(F::f64_mul(a, b)),
        3 => quiet64(F::f64_div(a, b)),
        4 | 5 => {
            if a & 0x7fff_ffff_ffff_ffff > 0x7ff0_0000_0000_0000
                || b & 0x7fff_ffff_ffff_ffff > 0x7ff0_0000_0000_0000
            {
                return 0x7ff8_0000_0000_0000;
            }
            if compare_float(0, a, b, 64) {
                if op == 4 {
                    a | b
                } else {
                    a & b
                }
            } else if compare_float(2, a, b, 64) == (op == 4) {
                a
            } else {
                b
            }
        }
        _ => (a & 0x7fff_ffff_ffff_ffff) | (b & 0x8000_0000_0000_0000),
    }
}

/// Exact f32-to-f64 promotion, with arithmetic NaNs canonicalized.
pub(super) fn promote(bits: u32) -> u64 {
    let sign = ((bits & 0x8000_0000) as u64) << 32;
    let exponent = (bits >> 23) & 255;
    let mut fraction = bits & 0x7f_ffff;
    if exponent == 255 {
        return if fraction == 0 {
            sign | 0x7ff0_0000_0000_0000
        } else {
            0x7ff8_0000_0000_0000
        };
    }
    if exponent != 0 {
        return sign | (((exponent + 896) as u64) << 52) | ((fraction as u64) << 29);
    }
    if fraction == 0 {
        return sign;
    }
    let mut exponent64 = 897u64;
    while fraction < 0x80_0000 {
        fraction <<= 1;
        exponent64 -= 1;
    }
    sign | (exponent64 << 52) | (((fraction & 0x7f_ffff) as u64) << 29)
}

fn overflow(negative: bool, width: u32, signed: bool, saturating: bool) -> Result<u64, ExecError> {
    if !saturating {
        return Err(ExecError::Trap(Trap::IntegerOverflow));
    }
    let maximum = if width == 32 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    Ok(if signed {
        if negative {
            1u64 << (width - 1)
        } else {
            maximum >> 1
        }
    } else if negative {
        0
    } else {
        maximum
    })
}

/// Truncates the IEEE significand using only integers. Bounds are checked after
/// discarding fractional bits, so negative values between -1 and 0 become zero.
pub(super) fn trunc_int(
    bits: u64,
    input32: bool,
    width: u32,
    signed: bool,
    saturating: bool,
) -> Result<u64, ExecError> {
    let (fraction_bits, bias, exponent_max, negative) = if input32 {
        (23u32, 127u32, 255u32, bits & 0x8000_0000 != 0)
    } else {
        (52, 1023, 2047, bits & 0x8000_0000_0000_0000 != 0)
    };
    let exponent = ((bits >> fraction_bits) as u32) & exponent_max;
    let fraction = bits & ((1u64 << fraction_bits) - 1);
    if exponent == exponent_max {
        if fraction != 0 {
            return if saturating {
                Ok(0)
            } else {
                Err(ExecError::Trap(Trap::InvalidConversionToInteger))
            };
        }
        return overflow(negative, width, signed, saturating);
    }
    if exponent < bias {
        return Ok(0);
    }
    let power = exponent - bias;
    if power >= 64 {
        return overflow(negative, width, signed, saturating);
    }
    let significand = fraction | (1u64 << fraction_bits);
    let magnitude = if power >= fraction_bits {
        significand << (power - fraction_bits)
    } else {
        significand >> (fraction_bits - power)
    };
    let maximum = if width == 32 {
        u32::MAX as u64
    } else {
        u64::MAX
    };
    let limit = if signed {
        if negative {
            1u64 << (width - 1)
        } else {
            maximum >> 1
        }
    } else {
        maximum
    };
    if magnitude > limit || (negative && !signed && magnitude != 0) {
        return overflow(negative, width, signed, saturating);
    }
    Ok(if negative {
        0u64.wrapping_sub(magnitude) & maximum
    } else {
        magnitude
    })
}

#[inline(always)]
pub(super) fn scalar<F: FloatOps>(opcode: u16, a: u64, b: u64) -> Result<u64, ExecError> {
    let result = match opcode {
        0x5b | 0x5c | 0x5d | 0x5e | 0x5f | 0x60 => {
            compare_float(opcode - 0x5b, a as u32 as u64, b as u32 as u64, 32) as u64
        }
        0x61 | 0x62 | 0x63 | 0x64 | 0x65 | 0x66 => compare_float(opcode - 0x61, a, b, 64) as u64,
        0x8b | 0x8c | 0x8d | 0x8e | 0x8f | 0x90 | 0x91 => {
            unary32::<F>(opcode - 0x8b, a as u32) as u64
        }
        0x92 | 0x93 | 0x94 | 0x95 | 0x96 | 0x97 | 0x98 => {
            binary32::<F>(opcode - 0x92, a as u32, b as u32) as u64
        }
        0x99 | 0x9a | 0x9b | 0x9c | 0x9d | 0x9e | 0x9f => unary64::<F>(opcode - 0x99, a),
        0xa0 | 0xa1 | 0xa2 | 0xa3 | 0xa4 | 0xa5 | 0xa6 => binary64::<F>(opcode - 0xa0, a, b),
        0xa8 | 0xa9 | 0xaa | 0xab | 0xae | 0xaf | 0xb0 | 0xb1 | 0x100 | 0x101 | 0x102 | 0x103
        | 0x104 | 0x105 | 0x106 | 0x107 => {
            let (op, width, saturating) = if opcode >= 0x100 {
                (opcode - 0x100, if opcode < 0x104 { 32 } else { 64 }, true)
            } else if opcode <= 0xab {
                (opcode - 0xa8, 32, false)
            } else {
                (opcode - 0xae, 64, false)
            };
            return trunc_int(a, op % 4 < 2, width, op % 2 == 0, saturating);
        }
        0xb2 => quiet32(F::f32_convert_i32_s(a as i32)) as u64,
        0xb3 => quiet32(F::f32_convert_i32_u(a as u32)) as u64,
        0xb4 => quiet32(F::f32_convert_i64_s(a as i64)) as u64,
        0xb5 => quiet32(F::f32_convert_i64_u(a)) as u64,
        0xb6 => quiet32(F::f32_demote_f64(a)) as u64,
        0xb7 => quiet64(F::f64_convert_i32_s(a as i32)),
        0xb8 => quiet64(F::f64_convert_i32_u(a as u32)),
        0xb9 => quiet64(F::f64_convert_i64_s(a as i64)),
        0xba => quiet64(F::f64_convert_i64_u(a)),
        0xbb => promote(a as u32),
        0xbc | 0xbe => a as u32 as u64,
        0xbd | 0xbf => a,
        _ => return Err(ExecError::BadArguments),
    };
    Ok(result)
}

#[cfg(all(test, not(charon)))]
mod tests {
    use super::super::super::native::NativeFloat;
    use super::*;

    fn check_f32(bits: u32) {
        let f = f32::from_bits(bits);
        let promoted = (f as f64).to_bits();
        assert_eq!(promote(bits), quiet64(promoted), "promotion {bits:x}");
        for (width, signed, expected) in [
            (32, true, f as i32 as u32 as u64),
            (32, false, f as u32 as u64),
            (64, true, f as i64 as u64),
            (64, false, f as u64),
        ] {
            assert_eq!(
                trunc_int(bits as u64, true, width, signed, true),
                Ok(expected),
                "trunc_sat {bits:x} {width} {signed}"
            );
        }
        let other = bits.rotate_left(13);
        let g = f32::from_bits(other);
        for (op, expected) in [
            (0, f == g),
            (1, f != g),
            (2, f < g),
            (3, f > g),
            (4, f <= g),
            (5, f >= g),
        ] {
            assert_eq!(
                compare_float(op, bits as u64, other as u64, 32),
                expected,
                "comparison {bits:x} {other:x}"
            );
        }
    }

    #[test]
    fn f32_all_exponents_and_boundary_significands() {
        for exponent in 0..256u32 {
            for fraction in [0, 1, 2, 0x3f_ffff, 0x40_0000, 0x7f_fffe, 0x7f_ffff] {
                check_f32((exponent << 23) | fraction);
                check_f32(0x8000_0000 | (exponent << 23) | fraction);
            }
        }
    }

    #[test]
    fn exact_float_random_differential() {
        let mut random = 0x6745_2301_efcd_ab89u64;
        for _ in 0..100_000 {
            random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
            check_f32(random as u32);
            let f = f64::from_bits(random);
            for (width, signed, expected) in [
                (32, true, f as i32 as u32 as u64),
                (32, false, f as u32 as u64),
                (64, true, f as i64 as u64),
                (64, false, f as u64),
            ] {
                assert_eq!(trunc_int(random, false, width, signed, true), Ok(expected));
            }
        }
    }

    /// Full binary32 coverage; run explicitly with --release --ignored.
    #[test]
    #[ignore = "exhaustive 2^32 input differential test; use --release"]
    fn exhaustive_f32_exact_operations() {
        let mut bits = 0u64;
        while bits <= u32::MAX as u64 {
            check_f32(bits as u32);
            bits += 1;
        }
    }

    #[test]
    fn trapping_bounds_signed_zero_nan_and_rounding() {
        assert_eq!(
            trunc_int((-2147483648.75f64).to_bits(), false, 32, true, false),
            Ok(0x8000_0000)
        );
        assert_eq!(
            trunc_int((-0.99f64).to_bits(), false, 32, false, false),
            Ok(0)
        );
        assert_eq!(
            trunc_int(2147483648f64.to_bits(), false, 32, true, false),
            Err(ExecError::Trap(Trap::IntegerOverflow))
        );
        assert_eq!(
            trunc_int(18446744073709551616f64.to_bits(), false, 64, false, false),
            Err(ExecError::Trap(Trap::IntegerOverflow))
        );
        assert_eq!(
            trunc_int(f64::NAN.to_bits(), false, 64, false, false),
            Err(ExecError::Trap(Trap::InvalidConversionToInteger))
        );
        assert_eq!(binary32::<NativeFloat>(4, 0, 0x8000_0000), 0x8000_0000);
        assert_eq!(binary32::<NativeFloat>(5, 0x8000_0000, 0), 0);
        assert_eq!(unary32::<NativeFloat>(0, 0xff80_0001), 0x7f80_0001);
        assert_eq!(
            unary64::<NativeFloat>(5, (-0.5f64).to_bits()),
            (-0.0f64).to_bits()
        );
        assert_eq!(
            unary64::<NativeFloat>(5, 2.5f64.to_bits()),
            2.0f64.to_bits()
        );
        assert_eq!(
            unary64::<NativeFloat>(5, 3.5f64.to_bits()),
            4.0f64.to_bits()
        );
    }
}
