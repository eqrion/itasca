//! Embedding boundaries used by the generic interpreter.

use super::{Store, Value};
use alloc::vec::Vec;

/// A synchronous interrupt decision at a function entry or loop header.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum InterruptAction {
    Continue,
    Terminate,
}

/// A failure reported by a synchronous host function.
#[derive(Clone, Copy)]
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
pub enum HostError {
    Trap,
    StackOverflow,
}

/// Synchronous embedding hooks. Each hook must return without panicking.
///
/// Interrupt hooks must not access or mutate Wasm state. Host calls may mutate
/// the supplied store through its public API and invoke Wasm recursively using
/// a separate execution. Result slots start with zero values of the declared
/// result types. Successful host results are checked before use.
pub trait Platform<M: MemoryBuffer> {
    fn interrupt(&mut self) -> InterruptAction;
    fn call_host(
        &mut self,
        store: &mut Store<M>,
        host_id: u64,
        args: &[Value],
        results: &mut [Value],
    ) -> Result<(), HostError>;
}

/// A linear-memory buffer whose size can change only through `grow`.
///
/// Construction succeeds with exactly `len` zero bytes. Growing succeeds with
/// exactly `new_len` bytes, preserving old bytes and zeroing the added suffix;
/// failure leaves all bytes unchanged. `bytes_mut` preserves length and changes
/// are observed by `bytes`. Methods must return without panicking. Outside host
/// calls, the embedding must not modify the buffer independently.
pub trait MemoryBuffer: Sized {
    fn new_zeroed(len: usize) -> Option<Self>;
    fn bytes(&self) -> &[u8];
    fn bytes_mut(&mut self) -> &mut [u8];
    fn grow(&mut self, new_len: usize) -> bool;
}

/// IEEE rounding operations over raw float bits.
///
/// Implementations use round-to-nearest-even without flushing subnormals or
/// fast-math transformations and return without panicking. The interpreter
/// canonicalizes arithmetic NaNs.
pub trait FloatOps {
    fn f32_add(a: u32, b: u32) -> u32;
    fn f32_sub(a: u32, b: u32) -> u32;
    fn f32_mul(a: u32, b: u32) -> u32;
    fn f32_div(a: u32, b: u32) -> u32;
    fn f32_sqrt(a: u32) -> u32;
    fn f32_ceil(a: u32) -> u32;
    fn f32_floor(a: u32) -> u32;
    fn f32_trunc(a: u32) -> u32;
    fn f32_nearest(a: u32) -> u32;
    fn f32_convert_i32_s(a: i32) -> u32;
    fn f32_convert_i32_u(a: u32) -> u32;
    fn f32_convert_i64_s(a: i64) -> u32;
    fn f32_convert_i64_u(a: u64) -> u32;
    fn f64_add(a: u64, b: u64) -> u64;
    fn f64_sub(a: u64, b: u64) -> u64;
    fn f64_mul(a: u64, b: u64) -> u64;
    fn f64_div(a: u64, b: u64) -> u64;
    fn f64_sqrt(a: u64) -> u64;
    fn f64_ceil(a: u64) -> u64;
    fn f64_floor(a: u64) -> u64;
    fn f64_trunc(a: u64) -> u64;
    fn f64_nearest(a: u64) -> u64;
    fn f64_convert_i32_s(a: i32) -> u64;
    fn f64_convert_i32_u(a: u32) -> u64;
    fn f64_convert_i64_s(a: i64) -> u64;
    fn f64_convert_i64_u(a: u64) -> u64;
    fn f32_demote_f64(a: u64) -> u32;
}

/// Fallible capacity reservation. Implementations preserve vector contents and
/// return without panicking. A true result provides capacity for `additional`
/// more elements; failure may be reported even when capacity was available.
pub(crate) trait Alloc {
    fn reserve<T>(values: &mut Vec<T>, additional: usize) -> bool;
}

/// The default linear memory backed by a growable byte vector.
pub struct VecMemory {
    pub(crate) data: Vec<u8>,
}

impl VecMemory {
    pub(crate) fn new_zeroed_with<A: Alloc>(len: usize) -> Option<Self> {
        let mut memory = Self { data: Vec::new() };
        if memory.grow_with::<A>(len) {
            Some(memory)
        } else {
            None
        }
    }
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.data
    }
    pub(crate) fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }
    pub(crate) fn grow_with<A: Alloc>(&mut self, new_len: usize) -> bool {
        if new_len < self.data.len() {
            return false;
        }
        let additional = new_len - self.data.len();
        if !A::reserve(&mut self.data, additional) {
            return false;
        }
        while self.data.len() < new_len {
            self.data.push(0);
        }
        true
    }
}
