//! Allocation-free views of block parameters and results.
//!
//! Indexed descriptors resolve against the module environment and check their type
//! indices before accessing storage.

use crate::error::OpError;
use crate::metadata::Env;
use crate::reader::{read_byte, read_s33_leb};
use crate::wasm_types::ValueType;

/// The parameter or result part of an indexed function signature.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum TypePart {
    Params,
    Results,
}

/// An empty, singleton, or indexed sequence of value types.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum ResultType {
    Empty,
    One(ValueType),
    Type { index: u32, part: TypePart },
}

impl ResultType {
    pub fn len(&self, env: &Env) -> Result<usize, OpError> {
        match self {
            ResultType::Empty => Ok(0),
            ResultType::One(_) => Ok(1),
            ResultType::Type { index, part } => {
                let i = *index as usize;
                if i >= env.types.len() {
                    return Err(OpError::UnknownType);
                }
                match part {
                    TypePart::Params => Ok(env.types[i].params.len()),
                    TypePart::Results => Ok(env.types[i].results.len()),
                }
            }
        }
    }

    /// Resolves one value type, returning `None` for an out-of-range element.
    ///
    /// An invalid type index returns `OpError::UnknownType` before indexing
    /// storage.
    pub fn get(&self, env: &Env, element: usize) -> Result<Option<ValueType>, OpError> {
        match self {
            ResultType::Empty => Ok(None),
            ResultType::One(v) => {
                if element == 0 {
                    Ok(Some(*v))
                } else {
                    Ok(None)
                }
            }
            ResultType::Type { index, part } => {
                let i = *index as usize;
                if i >= env.types.len() {
                    return Err(OpError::UnknownType);
                }
                match part {
                    TypePart::Params => {
                        if element >= env.types[i].params.len() {
                            Ok(None)
                        } else {
                            Ok(Some(env.types[i].params[element]))
                        }
                    }
                    TypePart::Results => {
                        if element >= env.types[i].results.len() {
                            Ok(None)
                        } else {
                            Ok(Some(env.types[i].results[element]))
                        }
                    }
                }
            }
        }
    }
}

/// A block's encoded signature: empty, one result, or a type-section index.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum BlockType {
    Empty,
    Value(ValueType),
    TypeIndex(u32),
}

impl BlockType {
    /// Returns the parameter descriptor of this block signature.
    pub fn params(&self) -> ResultType {
        match self {
            BlockType::TypeIndex(index) => ResultType::Type {
                index: *index,
                part: TypePart::Params,
            },
            _ => ResultType::Empty,
        }
    }

    /// Returns the result descriptor of this block signature.
    pub fn results(&self) -> ResultType {
        match self {
            BlockType::Empty => ResultType::Empty,
            BlockType::Value(v) => ResultType::One(*v),
            BlockType::TypeIndex(index) => ResultType::Type {
                index: *index,
                part: TypePart::Results,
            },
        }
    }
}

/// Decodes an empty or value-type block tag, or a nonnegative signed-33-bit type
/// index.
///
/// Padded negative tags are rejected instead of being interpreted as value
/// types.
pub(crate) fn read_block_type(data: &[u8], pos: usize) -> Result<(BlockType, usize), OpError> {
    let (b, p) = read_byte(data, pos)?;
    match b {
        0x40 => Ok((BlockType::Empty, p)),
        0x7f => Ok((BlockType::Value(ValueType::I32), p)),
        0x7e => Ok((BlockType::Value(ValueType::I64), p)),
        0x7d => Ok((BlockType::Value(ValueType::F32), p)),
        0x7c => Ok((BlockType::Value(ValueType::F64), p)),
        0x7b => Ok((BlockType::Value(ValueType::V128), p)),
        0x70 => Ok((BlockType::Value(ValueType::FuncRef), p)),
        0x6f => Ok((BlockType::Value(ValueType::ExternRef), p)),
        _ => {
            let (index, end) = read_s33_leb(data, pos)?;
            if index < 0 {
                return Err(OpError::InvalidBlockType);
            }
            Ok((BlockType::TypeIndex(index as u32), end))
        }
    }
}
