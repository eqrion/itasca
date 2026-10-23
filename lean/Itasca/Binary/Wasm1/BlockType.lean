import Itasca.Binary.Wasm2.BlockType

/-!
# Wasm 1.0 block types

`ScalarBlockByte bt b` relates the empty block type and the four number result types that
Wasm 1.0 admits to their one-byte spelling. Every other block type is outside the Wasm 1.0
grammar.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- The one-byte spelling of a Wasm 1.0 block type. -/
inductive ScalarBlockByte : signature.BlockType → U8 → Prop where
  | empty : ScalarBlockByte .Empty 0x40#u8
  | i32 : ScalarBlockByte (.Value .I32) 0x7F#u8
  | i64 : ScalarBlockByte (.Value .I64) 0x7E#u8
  | f32 : ScalarBlockByte (.Value .F32) 0x7D#u8
  | f64 : ScalarBlockByte (.Value .F64) 0x7C#u8

/-- A byte spells at most one block type, and a block type has at most one spelling. -/
theorem ScalarBlockByte.unique {bt bt' b b'} (h : ScalarBlockByte bt b) (h' : ScalarBlockByte bt' b')
    (he : b = b' ∨ bt = bt') : bt = bt' ∧ b = b' := by
  cases h <;> cases h' <;> simp_all <;> contradiction

end Itasca.Wasm1
