//! Byte readers with explicit input and cursor arguments.
//!
//! Readers return the decoded value and next cursor. Module and body validation
//! share these functions. LEB decoding uses multiplication, division, and remainder
//! to preserve the verified arithmetic model.

use crate::error::OpError;

type Result<T> = core::result::Result<T, OpError>;

/// Reads one byte at `pos` and returns the next cursor.
pub fn read_byte(data: &[u8], pos: usize) -> Result<(u8, usize)> {
    if pos >= data.len() {
        return Err(OpError::UnexpectedEof);
    }
    let b = data[pos];
    Ok((b, pos + 1))
}

/// Reads an unsigned 32-bit LEB, checking its five-byte and final-byte bounds.
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

/// Reads a signed LEB within `[lo, hi]` using at most `last + 1` bytes.
///
/// An `i128` accumulator accommodates the tenth-byte multiplier for signed 64-bit
/// values before the final range check.
fn read_sn_leb(data: &[u8], pos: usize, last: u32, lo: i128, hi: i128) -> Result<(i128, usize)> {
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

/// Reads a signed 32-bit LEB and returns its value and next cursor.
pub fn read_s32_leb(data: &[u8], pos: usize) -> Result<(i32, usize)> {
    let (v, p) = read_sn_leb(data, pos, 4, -2147483648, 2147483647)?;
    Ok((v as i32, p))
}

/// Reads a signed 64-bit LEB and checks its tenth-byte bound.
pub fn read_s64_leb(data: &[u8], pos: usize) -> Result<(i64, usize)> {
    let (v, p) = read_sn_leb(data, pos, 9, -9223372036854775808, 9223372036854775807)?;
    Ok((v as i64, p))
}

/// Reads `n` little-endian bytes as a raw floating-point bit pattern.
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

/// Reads the exact `f32` immediate bits without interpreting the float value.
pub fn read_f32_bits(data: &[u8], pos: usize) -> Result<(u32, usize)> {
    let (v, p) = read_fn_bits(data, pos, 4)?;
    Ok((v as u32, p))
}

/// Reads the exact `f64` immediate bits without interpreting the float value.
pub fn read_f64_bits(data: &[u8], pos: usize) -> Result<(u64, usize)> {
    read_fn_bits(data, pos, 8)
}

/// Reads a signed 33-bit LEB for an indexed multi-value block signature.
pub fn read_s33_leb(data: &[u8], pos: usize) -> Result<(i64, usize)> {
    let (v, p) = read_sn_leb(data, pos, 4, -4294967296, 4294967295)?;
    Ok((v as i64, p))
}
