//! Bounds-checked scalar memory operations in little-endian byte order.
use super::*;
fn address(addr: u32, offset: u32, len: usize, bytes: usize) -> Result<usize, ExecError> {
    let start = addr as u64 + offset as u64;
    if start > bytes as u64 || len as u64 > bytes as u64 - start {
        return Err(Trap::MemoryOutOfBounds.into());
    }
    Ok(start as usize)
}
#[inline(always)]
pub(super) fn load(op: u16, addr: u32, offset: u32, bytes: &[u8]) -> Result<u64, ExecError> {
    let n = match op {
        0x28 | 0x2a | 0x34 | 0x35 => 4,
        0x29 | 0x2b => 8,
        0x2e | 0x2f | 0x32 | 0x33 => 2,
        _ => 1,
    };
    let start = address(addr, offset, n, bytes.len())?;
    let mut x = 0u64;
    let mut i = 0;
    while i < n {
        x |= (bytes[start + i] as u64) << (i * 8);
        i += 1;
    }
    Ok(match op {
        0x2c => (x as i8 as i32 as u32) as u64,
        0x2e => (x as i16 as i32 as u32) as u64,
        0x30 => x as i8 as i64 as u64,
        0x32 => x as i16 as i64 as u64,
        0x34 => x as i32 as i64 as u64,
        _ => x,
    })
}
#[inline(always)]
pub(super) fn store(
    op: u16,
    addr: u32,
    offset: u32,
    value: u64,
    bytes: &mut [u8],
) -> Result<(), ExecError> {
    let n = match op {
        0x36 | 0x38 | 0x3e => 4,
        0x37 | 0x39 => 8,
        0x3b | 0x3d => 2,
        _ => 1,
    };
    let start = address(addr, offset, n, bytes.len())?;
    let mut i = 0;
    while i < n {
        bytes[start + i] = (value >> (i * 8)) as u8;
        i += 1;
    }
    Ok(())
}
