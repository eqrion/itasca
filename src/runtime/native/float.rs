//! Native IEEE implementation, excluded from extraction.
use crate::runtime::FloatOps;

pub(crate) struct NativeFloat;

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

impl FloatOps for NativeFloat {
    fn f32_add(a: u32, b: u32) -> u32 {
        (f32::from_bits(a) + f32::from_bits(b)).to_bits()
    }
    fn f32_sub(a: u32, b: u32) -> u32 {
        (f32::from_bits(a) - f32::from_bits(b)).to_bits()
    }
    fn f32_mul(a: u32, b: u32) -> u32 {
        (f32::from_bits(a) * f32::from_bits(b)).to_bits()
    }
    fn f32_div(a: u32, b: u32) -> u32 {
        (f32::from_bits(a) / f32::from_bits(b)).to_bits()
    }
    fn f32_sqrt(a: u32) -> u32 {
        libm::sqrtf(f32::from_bits(a)).to_bits()
    }
    fn f32_ceil(a: u32) -> u32 {
        libm::ceilf(f32::from_bits(a)).to_bits()
    }
    fn f32_floor(a: u32) -> u32 {
        libm::floorf(f32::from_bits(a)).to_bits()
    }
    fn f32_trunc(a: u32) -> u32 {
        libm::truncf(f32::from_bits(a)).to_bits()
    }
    fn f32_nearest(a: u32) -> u32 {
        nearest32(f32::from_bits(a)).to_bits()
    }
    fn f32_convert_i32_s(a: i32) -> u32 {
        (a as f32).to_bits()
    }
    fn f32_convert_i32_u(a: u32) -> u32 {
        (a as f32).to_bits()
    }
    fn f32_convert_i64_s(a: i64) -> u32 {
        (a as f32).to_bits()
    }
    fn f32_convert_i64_u(a: u64) -> u32 {
        (a as f32).to_bits()
    }
    fn f64_add(a: u64, b: u64) -> u64 {
        (f64::from_bits(a) + f64::from_bits(b)).to_bits()
    }
    fn f64_sub(a: u64, b: u64) -> u64 {
        (f64::from_bits(a) - f64::from_bits(b)).to_bits()
    }
    fn f64_mul(a: u64, b: u64) -> u64 {
        (f64::from_bits(a) * f64::from_bits(b)).to_bits()
    }
    fn f64_div(a: u64, b: u64) -> u64 {
        (f64::from_bits(a) / f64::from_bits(b)).to_bits()
    }
    fn f64_sqrt(a: u64) -> u64 {
        libm::sqrt(f64::from_bits(a)).to_bits()
    }
    fn f64_ceil(a: u64) -> u64 {
        libm::ceil(f64::from_bits(a)).to_bits()
    }
    fn f64_floor(a: u64) -> u64 {
        libm::floor(f64::from_bits(a)).to_bits()
    }
    fn f64_trunc(a: u64) -> u64 {
        libm::trunc(f64::from_bits(a)).to_bits()
    }
    fn f64_nearest(a: u64) -> u64 {
        nearest64(f64::from_bits(a)).to_bits()
    }
    fn f64_convert_i32_s(a: i32) -> u64 {
        (a as f64).to_bits()
    }
    fn f64_convert_i32_u(a: u32) -> u64 {
        (a as f64).to_bits()
    }
    fn f64_convert_i64_s(a: i64) -> u64 {
        (a as f64).to_bits()
    }
    fn f64_convert_i64_u(a: u64) -> u64 {
        (a as f64).to_bits()
    }
    fn f32_demote_f64(a: u64) -> u32 {
        (f64::from_bits(a) as f32).to_bits()
    }
}
