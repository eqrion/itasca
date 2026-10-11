//! Allocation-free views of block parameters and results.
//!
//! A view owns no types: a multi-value signature refers to the type section.
//! Resolving an untrusted descriptor checks its index before accessing storage.

use crate::error::OpError;
use crate::module::Env;
use crate::reader::{read_byte, read_s33_leb};
use crate::types::ValueType;

#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum TypePart {
    Params,
    Results,
}

/// An empty, inline singleton, or indexed sequence of value types.
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

    /// Returns `None` for an out-of-range element, and an error for an
    /// out-of-range type index. Neither case performs unchecked indexing.
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

/// The encoded block immediate, kept distinct from a resolved result view.
#[cfg_attr(not(charon), derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
pub enum BlockType {
    Empty,
    Value(ValueType),
    TypeIndex(u32),
}

impl BlockType {
    pub fn params(&self) -> ResultType {
        match self {
            BlockType::TypeIndex(index) => ResultType::Type {
                index: *index,
                part: TypePart::Params,
            },
            _ => ResultType::Empty,
        }
    }

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

/// Decode the multi-value block grammar: a literal empty/value tag, or a
/// nonnegative s33 type index. Padded negative tags are not value types.
pub(crate) fn read_block_type(data: &[u8], pos: usize) -> Result<(BlockType, usize), OpError> {
    let (b, p) = read_byte(data, pos)?;
    match b {
        0x40 => Ok((BlockType::Empty, p)),
        0x7f => Ok((BlockType::Value(ValueType::I32), p)),
        0x7e => Ok((BlockType::Value(ValueType::I64), p)),
        0x7d => Ok((BlockType::Value(ValueType::F32), p)),
        0x7c => Ok((BlockType::Value(ValueType::F64), p)),
        _ => {
            let (index, end) = read_s33_leb(data, pos)?;
            if index < 0 {
                return Err(OpError::InvalidBlockType);
            }
            Ok((BlockType::TypeIndex(index as u32), end))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::FuncType;

    #[test]
    fn views_resolve_without_owning_signature_storage() {
        let mut env = Env::new();
        env.types.push(FuncType {
            params: alloc::vec![ValueType::I32, ValueType::F64],
            results: alloc::vec![ValueType::I64, ValueType::F32, ValueType::I32],
        });
        let block = BlockType::TypeIndex(0);
        assert_eq!(block.params().len(&env), Ok(2));
        assert_eq!(block.results().len(&env), Ok(3));
        assert_eq!(block.params().get(&env, 1), Ok(Some(ValueType::F64)));
        assert_eq!(block.results().get(&env, 1), Ok(Some(ValueType::F32)));
        assert_eq!(block.results().get(&env, 3), Ok(None));
        assert_eq!(block.results().get(&env, usize::MAX), Ok(None));
        assert_eq!(
            BlockType::TypeIndex(u32::MAX).params().len(&env),
            Err(OpError::UnknownType)
        );
        assert_eq!(
            BlockType::TypeIndex(1).results().get(&env, 0),
            Err(OpError::UnknownType)
        );
        assert_eq!(ResultType::Empty.get(&env, 0), Ok(None));
        assert_eq!(
            ResultType::One(ValueType::I32).get(&env, 0),
            Ok(Some(ValueType::I32))
        );
        assert_eq!(ResultType::One(ValueType::I32).get(&env, 1), Ok(None));
    }

    #[test]
    fn block_type_uses_signed_33_bit_indices() {
        assert_eq!(read_block_type(&[0x40], 0), Ok((BlockType::Empty, 1)));
        assert_eq!(
            read_block_type(&[0x7f], 0),
            Ok((BlockType::Value(ValueType::I32), 1))
        );
        assert_eq!(read_block_type(&[0], 0), Ok((BlockType::TypeIndex(0), 1)));
        assert_eq!(
            read_block_type(&[0x3f], 0),
            Ok((BlockType::TypeIndex(63), 1))
        );
        assert_eq!(
            read_block_type(&[0xc0, 0], 0),
            Ok((BlockType::TypeIndex(64), 2))
        );
        assert_eq!(
            read_block_type(&[0xff, 0], 0),
            Ok((BlockType::TypeIndex(127), 2))
        );
        assert_eq!(
            read_block_type(&[0xff, 0xff, 0xff, 0xff, 0x0f], 0),
            Ok((BlockType::TypeIndex(u32::MAX), 5))
        );
        // Legal nonminimal index, and a cursor with an untouched suffix.
        assert_eq!(
            read_block_type(&[9, 0x80, 0x80, 0x80, 0x80, 0, 9], 1),
            Ok((BlockType::TypeIndex(0), 6))
        );
    }

    #[test]
    fn reject_padded_negative_tags_and_invalid_indices() {
        for tag in [0x40, 0x7f, 0x7e, 0x7d, 0x7c] {
            assert_eq!(
                read_block_type(&[tag + 128, 0x7f], 0),
                Err(OpError::InvalidBlockType)
            );
        }
        assert_eq!(read_block_type(&[0x7b], 0), Err(OpError::InvalidBlockType));
        assert_eq!(
            read_block_type(&[0x80, 0x80, 0x80, 0x80, 0x10], 0),
            Err(OpError::LebTooLong)
        );
        assert_eq!(
            read_block_type(&[0x80, 0x80, 0x80, 0x80, 0x6f], 0),
            Err(OpError::LebTooLong)
        );
        assert_eq!(
            read_block_type(&[0x80, 0x80, 0x80, 0x80, 0x80, 0], 0),
            Err(OpError::LebTooLong)
        );
        assert_eq!(read_block_type(&[0x80], 0), Err(OpError::UnexpectedEof));
        assert_eq!(
            read_block_type(&[], usize::MAX),
            Err(OpError::UnexpectedEof)
        );
    }
}
