//! Byte-level reads over `(data, pos)`.
//!
//! There's no cursor type: each reader takes a position and returns the
//! position it stopped at, and the caller threads it through. Both the
//! function-body validator and the module decoder read through these
//! functions rather than duplicating the decoding logic.
//!
//! LEB128 decoding uses multiplication, division, and remainder rather than
//! bit shifts and masks.

use crate::error::OpError;

type Result<T> = core::result::Result<T, OpError>;

/// Reads one byte at `pos`.
pub fn read_byte(data: &[u8], pos: usize) -> Result<(u8, usize)> {
    if pos >= data.len() {
        return Err(OpError::UnexpectedEof);
    }
    let b = data[pos];
    Ok((b, pos + 1))
}

/// LEB128 unsigned 32-bit, rejecting encodings longer than five bytes and
/// fifth bytes carrying more than the four bits a `u32` has room for.
pub fn read_u32_leb(data: &[u8], pos: usize) -> Result<(u32, usize)> {
    let mut acc: u32 = 0;
    let mut mult: u32 = 1;
    let mut p: usize = pos;
    let mut i: u32 = 0;
    loop {
        if p >= data.len() {
            return Err(OpError::UnexpectedEof);
        }
        let b = data[p];
        p += 1;
        let low = b % 128;
        if i == 4 && low > 15 {
            return Err(OpError::LebTooLong);
        }
        acc = acc + (low as u32) * mult;
        if b < 128 {
            return Ok((acc, p));
        }
        if i == 4 {
            return Err(OpError::LebTooLong);
        }
        mult = mult * 128;
        i += 1;
    }
}

/// LEB128 signed, in at most `last + 1` bytes and within `[lo, hi]`. The
/// specification's `sN` rules are parametric in exactly this way (spec
/// 5.2.2), so one reader serves both widths.
///
/// The accumulator is `i128` rather than `i64` because `mult` reaches
/// `128^9`, which is `2^63`: a 64-bit accumulator would overflow on the
/// tenth byte of an s64, before the final range check gets a chance to
/// reject it.
fn read_sn_leb(
    data: &[u8],
    pos: usize,
    last: u32,
    lo: i128,
    hi: i128,
) -> Result<(i128, usize)> {
    let mut acc: i128 = 0;
    let mut mult: i128 = 1;
    let mut p: usize = pos;
    let mut i: u32 = 0;
    loop {
        if p >= data.len() {
            return Err(OpError::UnexpectedEof);
        }
        let b = data[p];
        p += 1;
        let low = b % 128;
        acc = acc + (low as i128) * mult;
        if b < 128 {
            // Sign-extend if the payload's high bit is set.
            if low >= 64 {
                acc = acc - mult * 128;
            }
            if acc < lo || acc > hi {
                return Err(OpError::LebTooLong);
            }
            return Ok((acc, p));
        }
        if i == last {
            return Err(OpError::LebTooLong);
        }
        mult = mult * 128;
        i += 1;
    }
}

/// LEB128 signed 32-bit. Only the value's presence matters for validation, so
/// the decoded number is returned but never inspected by the checker.
pub fn read_s32_leb(data: &[u8], pos: usize) -> Result<(i32, usize)> {
    let (v, p) = read_sn_leb(data, pos, 4, -2147483648, 2147483647)?;
    Ok((v as i32, p))
}

/// LEB128 signed 64-bit: ten bytes at most, the tenth carrying one bit.
pub fn read_s64_leb(data: &[u8], pos: usize) -> Result<(i64, usize)> {
    let (v, p) = read_sn_leb(
        data,
        pos,
        9,
        -9223372036854775808,
        9223372036854775807,
    )?;
    Ok((v as i64, p))
}

/// Spec 5.2.3: `fN ::= b*:byte^(N/8)`, the IEEE 754 bit pattern in
/// little-endian byte order. One loop for both widths, with the byte count
/// as a parameter.
fn read_fn_bits(data: &[u8], pos: usize, n: u32) -> Result<(u64, usize)> {
    let mut acc: u64 = 0;
    let mut mult: u64 = 1;
    let mut p: usize = pos;
    let mut i: u32 = 0;
    loop {
        if i == n {
            return Ok((acc, p));
        }
        if p >= data.len() {
            return Err(OpError::UnexpectedEof);
        }
        let b = data[p];
        p += 1;
        acc = acc + (b as u64) * mult;
        i += 1;
        // Returning here rather than at the top of the loop keeps
        // `mult == 256^i` an invariant: multiplying after the last byte would
        // reach `256^8`, which a `u64` cannot hold.
        if i == n {
            return Ok((acc, p));
        }
        mult = mult * 256;
    }
}

/// The bit pattern of an `f32` immediate. Bits rather than a float:
/// validation never inspects the value, and a consumer that wants it as a
/// float converts with `f32::from_bits`.
pub fn read_f32_bits(data: &[u8], pos: usize) -> Result<(u32, usize)> {
    let (v, p) = read_fn_bits(data, pos, 4)?;
    Ok((v as u32, p))
}

/// The bit pattern of an `f64` immediate. See [`read_f32_bits`].
pub fn read_f64_bits(data: &[u8], pos: usize) -> Result<(u64, usize)> {
    read_fn_bits(data, pos, 8)
}

// Declared here at the bottom so that adding them moved no line above: the
// extraction records a source line per definition and `Itasca_Funs.v` is
// generated and committed.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn leb128_single_byte() {
        assert_eq!(read_u32_leb(&[0x00], 0).unwrap(), (0, 1));
        assert_eq!(read_u32_leb(&[0x7f], 0).unwrap(), (127, 1));
    }

    #[test]
    fn leb128_multi_byte() {
        assert_eq!(read_u32_leb(&[0x80, 0x01], 0).unwrap(), (128, 2));
        assert_eq!(read_u32_leb(&[0xe5, 0x8e, 0x26], 0).unwrap(), (624485, 3));
    }

    #[test]
    fn leb128_u32_max() {
        let bytes = [0xff, 0xff, 0xff, 0xff, 0x0f];
        assert_eq!(read_u32_leb(&bytes, 0).unwrap(), (u32::MAX, 5));
    }

    #[test]
    fn leb128_rejects_more_than_five_bytes() {
        let bytes = [0x80, 0x80, 0x80, 0x80, 0x80, 0x00];
        assert!(read_u32_leb(&bytes, 0).is_err());
    }

    #[test]
    fn leb128_rejects_overflowing_fifth_byte() {
        // The fifth byte may contribute only four bits to a u32.
        let bytes = [0x80, 0x80, 0x80, 0x80, 0x10];
        assert!(read_u32_leb(&bytes, 0).is_err());
    }

    #[test]
    fn leb128_rejects_truncated_input() {
        assert!(read_u32_leb(&[0x80], 0).is_err());
        assert!(read_u32_leb(&[], 0).is_err());
    }

    #[test]
    fn leb128_signed_roundtrip() {
        assert_eq!(read_s32_leb(&[0x00], 0).unwrap(), (0, 1));
        assert_eq!(read_s32_leb(&[0x01], 0).unwrap(), (1, 1));
        assert_eq!(read_s32_leb(&[0x7f], 0).unwrap(), (-1, 1));
        assert_eq!(read_s32_leb(&[0x3f], 0).unwrap(), (63, 1));
        assert_eq!(read_s32_leb(&[0x40], 0).unwrap(), (-64, 1));
        assert_eq!(read_s32_leb(&[0xc0, 0xbb, 0x78], 0).unwrap(), (-123456, 3));
    }

    #[test]
    fn leb128_signed_32_rejects_out_of_range() {
        // Five bytes whose value is 2^31, one past i32::MAX.
        assert!(read_s32_leb(&[0x80, 0x80, 0x80, 0x80, 0x08], 0).is_err());
        assert!(read_s32_leb(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x00], 0).is_err());
    }

    #[test]
    fn leb128_signed_64_roundtrip() {
        assert_eq!(read_s64_leb(&[0x00], 0).unwrap(), (0, 1));
        assert_eq!(read_s64_leb(&[0x7f], 0).unwrap(), (-1, 1));
        assert_eq!(read_s64_leb(&[0xc0, 0xbb, 0x78], 0).unwrap(), (-123456, 3));
        // i64::MIN and i64::MAX, ten bytes each, the tenth carrying one bit.
        let min = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f];
        assert_eq!(read_s64_leb(&min, 0).unwrap(), (i64::MIN, 10));
        let max = [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00];
        assert_eq!(read_s64_leb(&max, 0).unwrap(), (i64::MAX, 10));
    }

    #[test]
    fn leb128_signed_64_rejects_out_of_range() {
        // An eleventh byte is one too many.
        let eleven = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00];
        assert!(read_s64_leb(&eleven, 0).is_err());
        // Ten bytes, but the tenth carries more than the one bit left.
        let wide = [0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x01];
        assert!(read_s64_leb(&wide, 0).is_err());
    }

    #[test]
    fn float_immediates_are_little_endian_bit_patterns() {
        assert_eq!(read_f32_bits(&[0x00, 0x00, 0x80, 0x3f], 0).unwrap(),
                   (0x3f800000, 4));
        assert_eq!(read_f64_bits(&[0, 0, 0, 0, 0, 0, 0xf0, 0x3f], 0).unwrap(),
                   (0x3ff0000000000000, 8));
        assert_eq!(read_f32_bits(&[0xff, 0xff, 0xff, 0xff], 0).unwrap(),
                   (u32::MAX, 4));
        assert_eq!(read_f64_bits(&[0xff; 8], 0).unwrap(), (u64::MAX, 8));
    }
}
