import Itasca.Generated.Funs

/-!
# Wasm 1.0 block types

The one-byte block type immediates: `Control.blockByte` is the byte of a block type,
`Control.ScalarBlockType` selects the empty type and the four number types that Wasm 1.0
admits, and `Control.BlockDecoded` describes a block type read at a cursor.
-/

open Aeneas Aeneas.Std

namespace Itasca.Control

/-- The single-byte spelling of a block type. `ScalarBlockType` restricts which of them belong to
the Wasm 1.0 grammar. -/
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

/-- A Wasm 1.0 block type spelled by the byte at the cursor, with the cursor advanced by one. -/
def BlockDecoded (data : Slice U8) (start : Usize) (bt : code.BlockType)
    (next : Usize) : Prop :=
  ∃ h : start.val < data.length,
    data.val[start.val] = blockByte bt ∧ next.val = start.val + 1 ∧
      next.val ≤ data.length ∧ ScalarBlockType bt

end Itasca.Control
