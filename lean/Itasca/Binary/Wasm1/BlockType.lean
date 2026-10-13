import Itasca.Generated.Funs

open Aeneas Aeneas.Std

/-! The one-byte block-type immediates of the Wasm 1.0 binary grammar. -/

namespace Itasca.Control

/-- Single-byte block-type spellings. `ScalarBlockType` separately restricts
which spellings belong to the Wasm 1.0 grammar and decoder. -/
def blockByte : code.BlockType → U8
  | .Empty => 64#u8
  | .Value .I32 => 127#u8
  | .Value .I64 => 126#u8
  | .Value .F32 => 125#u8
  | .Value .F64 => 124#u8
  | .Value .V128 => 123#u8
  | .Value .FuncRef => 112#u8
  | .Value .ExternRef => 111#u8

/-- The empty and four numeric result types admitted by Wasm 1.0 block headers. -/
def ScalarBlockType : code.BlockType → Prop
  | .Empty | .Value .I32 | .Value .I64 | .Value .F32 | .Value .F64 => True
  | _ => False

/-- An independently specified one-byte Wasm 1.0 block type. -/
def BlockDecoded (data : Slice U8) (start : Usize) (bt : code.BlockType)
    (next : Usize) : Prop :=
  ∃ h : start.val < data.length,
    data.val[start.val] = blockByte bt ∧ next.val = start.val + 1 ∧
      next.val ≤ data.length ∧ ScalarBlockType bt

end Itasca.Control
