//! Byte-level reads over `(data, pos)`.
//!
//! There is no cursor object: Aeneas rejects a struct that holds a borrow, so
//! the position is threaded explicitly and every reader returns the position it
//! stopped at. Both the function-body validator and the module decoder read
//! through these, which is why they live here rather than in either.
//!
//! No bitwise operators. `scalar_and`, `scalar_or` and `scalar_shl` are
//! unspecified axioms in Aeneas's `Primitives.v`, so LEB128 decoding uses
//! division and remainder, which have real definitions over `Z` and are
//! therefore provable.

use crate::error::OpError;

type Result<T> = core::result::Result<T, OpError>;

pub fn read_byte(data: &[u8], pos: usize) -> Result<(u8, usize)> {
    if pos >= data.len() {
        return Err(OpError::UnexpectedEof);
    }
    let b = data[pos];
    Ok((b, pos + 1))
}

/// LEB128 unsigned 32-bit, rejecting encodings longer than five bytes and
/// fifth bytes carrying more than the four bits a `u32` has room for.
///
/// `mult` is multiplied at most four times, reaching 2^28, and the accumulator
/// peaks at exactly `u32::MAX`, so neither can overflow. That matters because
/// an overflow would extract as `Fail_`, which the no-panic obligation forbids.
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
/// specification's `sN` rules are parametric in exactly this way (spec 5.2.2),
/// so one reader serves both widths and there is one correspondence proof.
///
/// The accumulator is `i128` rather than `i64` because `mult` reaches `128^9`,
/// which is `2^63`: a 64-bit accumulator overflows on the tenth byte of an s64,
/// and an overflow extracts as `Fail_`, which the no-panic obligation forbids.
/// A consumer free to use shift and mask does not need the wider type; this one
/// is not, since `scalar_shl` and `scalar_and` are unspecified axioms in
/// Aeneas's `Primitives.v`.
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

/// Spec 5.2.3: `fN ::= b*:byte^(N/8)`, the IEEE 754 bit pattern in little-endian
/// byte order. One loop for both widths, with the byte count as a parameter.
///
/// The accumulator is `u64` and never overflows: after `k < n <= 8` bytes it is
/// below `256^k`, and the next byte contributes at most `255 * 256^k`, so the sum
/// stays below `256^(k+1) <= 2^64`.
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

/// The bit pattern of an `f32` immediate. Bits rather than a float: the verified
/// core has no floating-point arithmetic, and validation does not need the value.
/// A compiler consumer reinterprets them as needed.
pub fn read_f32_bits(data: &[u8], pos: usize) -> Result<(u32, usize)> {
    let (v, p) = read_fn_bits(data, pos, 4)?;
    Ok((v as u32, p))
}

pub fn read_f64_bits(data: &[u8], pos: usize) -> Result<(u64, usize)> {
    read_fn_bits(data, pos, 8)
}
