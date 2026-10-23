//! Typed values at the API boundary and untagged interpreter slots.
use super::{ExternAddr, FuncAddr, Value};
use crate::ValueType;

/// Returns the number of 64-bit slots occupied by a value of type `ty`.
pub(crate) fn width(ty: ValueType) -> u32 {
    match ty {
        ValueType::V128 => 2,
        _ => 1,
    }
}
/// Returns the total slot width of `types`, or `None` if it exceeds `usize::MAX`.
pub(crate) fn type_slots(types: &[ValueType]) -> Option<usize> {
    let mut slots = 0usize;
    let mut i = 0;
    let mut overflow = false;
    while i < types.len() && !overflow {
        match slots.checked_add(width(types[i]) as usize) {
            Some(n) => slots = n,
            None => overflow = true,
        }
        i += 1;
    }
    if overflow {
        None
    } else {
        Some(slots)
    }
}
pub(crate) fn encode(value: Value) -> (u64, u64) {
    match value {
        Value::I32(v) | Value::F32(v) => (v as u64, 0),
        Value::I64(v) | Value::F64(v) => (v, 0),
        Value::V128(v) => (v as u64, (v >> 64) as u64),
        Value::FuncRef(None) | Value::ExternRef(None) => (0, 0),
        Value::FuncRef(Some(a)) => (a.index as u64 + 1, 0),
        Value::ExternRef(Some(a)) => (a.index as u64 + 1, 0),
    }
}
pub(crate) fn decode(ty: ValueType, lo: u64, hi: u64, store: usize) -> Value {
    match ty {
        ValueType::I32 => Value::I32(lo as u32),
        ValueType::I64 => Value::I64(lo),
        ValueType::F32 => Value::F32(lo as u32),
        ValueType::F64 => Value::F64(lo),
        ValueType::V128 => Value::V128(lo as u128 | ((hi as u128) << 64)),
        ValueType::FuncRef => Value::FuncRef(if lo == 0 {
            None
        } else {
            Some(FuncAddr {
                store,
                index: lo as usize - 1,
            })
        }),
        ValueType::ExternRef => Value::ExternRef(if lo == 0 {
            None
        } else {
            Some(ExternAddr {
                store,
                index: lo as usize - 1,
            })
        }),
    }
}
