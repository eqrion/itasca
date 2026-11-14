import Itasca.Support.Result
import Mathlib.Tactic.IntervalCases
import Itasca.Binary.Wasm2.Syntax
import Itasca.Binary.Wasm1.BlockType
import Itasca.Binary.SignedLeb32
import Itasca.Binary.SignedLeb64
import Itasca.Spec.TypingInversion

/-!
Sections, each formerly its own module: MemoryMeaning, NumericMeaning, Encoding, BrTableLabels, EncodingComplete.
-/

/-! ## MemoryMeaning -/

section

/-!
# Wasm 1.0 memory opcodes

`MemoryMeaning.opcodeMeaning` is a literal table from the load and store opcodes `0x28` to
`0x3e` to their value type, natural alignment and SpecTec instruction. It is written
independently of the extracted opcode dispatch.
-/

open Aeneas Aeneas.Std

namespace Itasca.MemoryMeaning

/-- The SpecTec memory argument of a Rust `MemArg`. -/
def memArg (arg : code.MemArg) : memarg :=
  { ALIGN := .mk_uN arg.align.val, OFFSET := .mk_uN arg.offset.val }

/-- A row of the memory opcode table: the value type, the natural alignment exponent, whether it is
a store, and the instruction built from a memory argument. -/
structure Operation where
  ty : wasm_types.ValueType
  naturalAlign : U32
  store : Bool
  op : code.MemArg → instr

/-- A load of the full width of a number type. -/
def fullLoad (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg => .LOAD nt none (memArg arg)⟩

/-- A packed integer load of the given bit width and signedness. -/
def packedLoad (ty : wasm_types.ValueType) (it : Inn) (width : Nat)
    (extension : sx) (alignment : U32) : Operation :=
  ⟨ty, alignment, false, fun arg =>
    .LOAD (numtype_Inn it) (some (.mk_loadop__0 it (.mk_loadop_Inn (.mk_sz width) extension))) (memArg arg)⟩

/-- A store of the full width of a number type. -/
def fullStore (ty : wasm_types.ValueType) (nt : numtype) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE nt none (memArg arg)⟩

/-- A packed integer store of the given bit width. -/
def packedStore (ty : wasm_types.ValueType) (it : Inn) (width : Nat) (alignment : U32) : Operation :=
  ⟨ty, alignment, true, fun arg => .STORE (numtype_Inn it) (some (.mk_sz width)) (memArg arg)⟩

/-- The load or store opcode table, transcribed from the Wasm 1.0 specification. -/
def opcodeMeaning (opcode : U8) : Option Operation :=
  match opcode.val with
  | 0x28 => some (fullLoad .I32 .I32 2#u32)
  | 0x29 => some (fullLoad .I64 .I64 3#u32)
  | 0x2A => some (fullLoad .F32 .F32 2#u32)
  | 0x2B => some (fullLoad .F64 .F64 3#u32)
  | 0x2C => some (packedLoad .I32 .I32 8 .S 0#u32)
  | 0x2D => some (packedLoad .I32 .I32 8 .U 0#u32)
  | 0x2E => some (packedLoad .I32 .I32 16 .S 1#u32)
  | 0x2F => some (packedLoad .I32 .I32 16 .U 1#u32)
  | 0x30 => some (packedLoad .I64 .I64 8 .S 0#u32)
  | 0x31 => some (packedLoad .I64 .I64 8 .U 0#u32)
  | 0x32 => some (packedLoad .I64 .I64 16 .S 1#u32)
  | 0x33 => some (packedLoad .I64 .I64 16 .U 1#u32)
  | 0x34 => some (packedLoad .I64 .I64 32 .S 2#u32)
  | 0x35 => some (packedLoad .I64 .I64 32 .U 2#u32)
  | 0x36 => some (fullStore .I32 .I32 2#u32)
  | 0x37 => some (fullStore .I64 .I64 3#u32)
  | 0x38 => some (fullStore .F32 .F32 2#u32)
  | 0x39 => some (fullStore .F64 .F64 3#u32)
  | 0x3A => some (packedStore .I32 .I32 8 0#u32)
  | 0x3B => some (packedStore .I32 .I32 16 1#u32)
  | 0x3C => some (packedStore .I64 .I64 8 0#u32)
  | 0x3D => some (packedStore .I64 .I64 16 1#u32)
  | 0x3E => some (packedStore .I64 .I64 32 2#u32)
  | _ => none

end Itasca.MemoryMeaning

end

/-! ## NumericMeaning -/

section

/-!
# Wasm 1.0 numeric opcodes

`Numeric.opcodeMeaning` is a literal table of the scalar numeric opcodes `0x45` to `0xbf`. Each
row is an `Numeric.Operation`: a SpecTec instruction with its operand and result types and a
proof that it is well formed and that `Instr_ok` types it with that stack effect. The table is
written independently of the extracted opcode dispatch.
-/

open Aeneas Aeneas.Std

namespace Itasca.Numeric

/-- A SpecTec number type as a Rust value type. -/
def valueType : numtype → wasm_types.ValueType
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64

/-- Translating `valueType t` gives the SpecTec value type of `t`. -/
@[simp] theorem numType_value (t : numtype) :
    Translate.valueType (valueType t) = valtype_numtype t := by cases t <;> rfl

/-- A scalar instruction with its operand and result types, and proofs that it is well formed and
typed by the generated rules with that effect. -/
structure Operation where
  instruction : instr
  input : wasm_types.ValueType
  output : wasm_types.ValueType
  binary : Bool
  wellFormed : wf_instr instruction
  typed : ∀ C, wf_context C → Instr_ok C instruction
    (.mk_functype (.mk_list ((if binary then [input, input] else [input]).map Translate.valueType))
      (.mk_list [Translate.valueType output]))

/-- The operand types of an operation. -/
def Operation.inputs (op : Operation) : List wasm_types.ValueType :=
  if op.binary then [op.input, op.input] else [op.input]

/-- A unary operation row. -/
def unary (t : numtype) (op : unop_) (hwf : wf_unop_ t op) : Operation where
  instruction := .UNOP t op
  input := valueType t
  output := valueType t
  binary := false
  wellFormed := .instr_case_14 _ _ hwf
  typed C hC := by
    have h := Instr_ok.unop C t op hC (.instr_case_14 _ _ hwf)
    cases t <;> simpa [valueType, Translate.valueType, valtype_numtype] using h

/-- A binary operation row. -/
def binary (t : numtype) (op : binop_) (hwf : wf_binop_ t op) : Operation where
  instruction := .BINOP t op
  input := valueType t
  output := valueType t
  binary := true
  wellFormed := .instr_case_15 _ _ hwf
  typed C hC := by
    have h := Instr_ok.binop C t op hC (.instr_case_15 _ _ hwf)
    cases t <;> simpa [valueType, Translate.valueType, valtype_numtype] using h

/-- A test operation row, which returns `i32`. -/
def test (t : numtype) (op : testop_) (hwf : wf_testop_ t op) : Operation where
  instruction := .TESTOP t op
  input := valueType t
  output := .I32
  binary := false
  wellFormed := .instr_case_16 _ _ hwf
  typed C hC := by
    have h := Instr_ok.testop C t op hC (.instr_case_16 _ _ hwf)
    cases t <;> simpa [valueType, Translate.valueType, valtype_numtype] using h

/-- A comparison operation row, which returns `i32`. -/
def relation (t : numtype) (op : relop_) (hwf : wf_relop_ t op) : Operation where
  instruction := .RELOP t op
  input := valueType t
  output := .I32
  binary := true
  wellFormed := .instr_case_17 _ _ hwf
  typed C hC := by
    have h := Instr_ok.relop C t op hC (.instr_case_17 _ _ hwf)
    cases t <;> simpa [valueType, Translate.valueType, valtype_numtype] using h

/-- A conversion operation row from `source` to `target`. -/
def conversion (source target : numtype) (op : cvtop__)
    (hwf : wf_cvtop__ source target op)
    (hne : target ≠ source) : Operation where
  instruction := .CVTOP target source op
  input := valueType source
  output := valueType target
  binary := false
  wellFormed := .instr_case_18 _ _ _ hwf hne
  typed C hC := by
    have h := Instr_ok.cvtop C target source op hC
      (.instr_case_18 _ _ _ hwf hne)
    cases source <;> cases target <;> simpa [valueType, Translate.valueType, valtype_numtype] using h

/-- The Wasm 1.0 scalar numeric opcode table. -/
def opcodeMeaning (opcode : U8) : Option Operation :=
  match opcode.val with
  | 0x45 => some (test .I32 (.mk_testop__0 .I32 .EQZ) (.testop__case_0 _ _ _ rfl))
  | 0x46 => some (relation .I32 (.mk_relop__0 .I32 (.EQ)) (.relop__case_0 _ _ _ rfl))
  | 0x47 => some (relation .I32 (.mk_relop__0 .I32 (.NE)) (.relop__case_0 _ _ _ rfl))
  | 0x48 => some (relation .I32 (.mk_relop__0 .I32 (.LT .S)) (.relop__case_0 _ _ _ rfl))
  | 0x49 => some (relation .I32 (.mk_relop__0 .I32 (.LT .U)) (.relop__case_0 _ _ _ rfl))
  | 0x4A => some (relation .I32 (.mk_relop__0 .I32 (.GT .S)) (.relop__case_0 _ _ _ rfl))
  | 0x4B => some (relation .I32 (.mk_relop__0 .I32 (.GT .U)) (.relop__case_0 _ _ _ rfl))
  | 0x4C => some (relation .I32 (.mk_relop__0 .I32 (.LE .S)) (.relop__case_0 _ _ _ rfl))
  | 0x4D => some (relation .I32 (.mk_relop__0 .I32 (.LE .U)) (.relop__case_0 _ _ _ rfl))
  | 0x4E => some (relation .I32 (.mk_relop__0 .I32 (.GE .S)) (.relop__case_0 _ _ _ rfl))
  | 0x4F => some (relation .I32 (.mk_relop__0 .I32 (.GE .U)) (.relop__case_0 _ _ _ rfl))
  | 0x50 => some (test .I64 (.mk_testop__0 .I64 .EQZ) (.testop__case_0 _ _ _ rfl))
  | 0x51 => some (relation .I64 (.mk_relop__0 .I64 (.EQ)) (.relop__case_0 _ _ _ rfl))
  | 0x52 => some (relation .I64 (.mk_relop__0 .I64 (.NE)) (.relop__case_0 _ _ _ rfl))
  | 0x53 => some (relation .I64 (.mk_relop__0 .I64 (.LT .S)) (.relop__case_0 _ _ _ rfl))
  | 0x54 => some (relation .I64 (.mk_relop__0 .I64 (.LT .U)) (.relop__case_0 _ _ _ rfl))
  | 0x55 => some (relation .I64 (.mk_relop__0 .I64 (.GT .S)) (.relop__case_0 _ _ _ rfl))
  | 0x56 => some (relation .I64 (.mk_relop__0 .I64 (.GT .U)) (.relop__case_0 _ _ _ rfl))
  | 0x57 => some (relation .I64 (.mk_relop__0 .I64 (.LE .S)) (.relop__case_0 _ _ _ rfl))
  | 0x58 => some (relation .I64 (.mk_relop__0 .I64 (.LE .U)) (.relop__case_0 _ _ _ rfl))
  | 0x59 => some (relation .I64 (.mk_relop__0 .I64 (.GE .S)) (.relop__case_0 _ _ _ rfl))
  | 0x5A => some (relation .I64 (.mk_relop__0 .I64 (.GE .U)) (.relop__case_0 _ _ _ rfl))
  | 0x5B => some (relation .F32 (.mk_relop__1 .F32 .EQ) (.relop__case_1 _ _ _ rfl))
  | 0x5C => some (relation .F32 (.mk_relop__1 .F32 .NE) (.relop__case_1 _ _ _ rfl))
  | 0x5D => some (relation .F32 (.mk_relop__1 .F32 .LT) (.relop__case_1 _ _ _ rfl))
  | 0x5E => some (relation .F32 (.mk_relop__1 .F32 .GT) (.relop__case_1 _ _ _ rfl))
  | 0x5F => some (relation .F32 (.mk_relop__1 .F32 .LE) (.relop__case_1 _ _ _ rfl))
  | 0x60 => some (relation .F32 (.mk_relop__1 .F32 .GE) (.relop__case_1 _ _ _ rfl))
  | 0x61 => some (relation .F64 (.mk_relop__1 .F64 .EQ) (.relop__case_1 _ _ _ rfl))
  | 0x62 => some (relation .F64 (.mk_relop__1 .F64 .NE) (.relop__case_1 _ _ _ rfl))
  | 0x63 => some (relation .F64 (.mk_relop__1 .F64 .LT) (.relop__case_1 _ _ _ rfl))
  | 0x64 => some (relation .F64 (.mk_relop__1 .F64 .GT) (.relop__case_1 _ _ _ rfl))
  | 0x65 => some (relation .F64 (.mk_relop__1 .F64 .LE) (.relop__case_1 _ _ _ rfl))
  | 0x66 => some (relation .F64 (.mk_relop__1 .F64 .GE) (.relop__case_1 _ _ _ rfl))
  | 0x67 => some (unary .I32 (.mk_unop__0 .I32 .CLZ) (.unop__case_0 _ _ _ rfl))
  | 0x68 => some (unary .I32 (.mk_unop__0 .I32 .CTZ) (.unop__case_0 _ _ _ rfl))
  | 0x69 => some (unary .I32 (.mk_unop__0 .I32 .POPCNT) (.unop__case_0 _ _ _ rfl))
  | 0x6A => some (binary .I32 (.mk_binop__0 .I32 (.ADD)) (.binop__case_0 _ _ _ rfl))
  | 0x6B => some (binary .I32 (.mk_binop__0 .I32 (.SUB)) (.binop__case_0 _ _ _ rfl))
  | 0x6C => some (binary .I32 (.mk_binop__0 .I32 (.MUL)) (.binop__case_0 _ _ _ rfl))
  | 0x6D => some (binary .I32 (.mk_binop__0 .I32 (.DIV .S)) (.binop__case_0 _ _ _ rfl))
  | 0x6E => some (binary .I32 (.mk_binop__0 .I32 (.DIV .U)) (.binop__case_0 _ _ _ rfl))
  | 0x6F => some (binary .I32 (.mk_binop__0 .I32 (.REM .S)) (.binop__case_0 _ _ _ rfl))
  | 0x70 => some (binary .I32 (.mk_binop__0 .I32 (.REM .U)) (.binop__case_0 _ _ _ rfl))
  | 0x71 => some (binary .I32 (.mk_binop__0 .I32 (.AND)) (.binop__case_0 _ _ _ rfl))
  | 0x72 => some (binary .I32 (.mk_binop__0 .I32 (.OR)) (.binop__case_0 _ _ _ rfl))
  | 0x73 => some (binary .I32 (.mk_binop__0 .I32 (.XOR)) (.binop__case_0 _ _ _ rfl))
  | 0x74 => some (binary .I32 (.mk_binop__0 .I32 (.SHL)) (.binop__case_0 _ _ _ rfl))
  | 0x75 => some (binary .I32 (.mk_binop__0 .I32 (.SHR .S)) (.binop__case_0 _ _ _ rfl))
  | 0x76 => some (binary .I32 (.mk_binop__0 .I32 (.SHR .U)) (.binop__case_0 _ _ _ rfl))
  | 0x77 => some (binary .I32 (.mk_binop__0 .I32 (.ROTL)) (.binop__case_0 _ _ _ rfl))
  | 0x78 => some (binary .I32 (.mk_binop__0 .I32 (.ROTR)) (.binop__case_0 _ _ _ rfl))
  | 0x79 => some (unary .I64 (.mk_unop__0 .I64 .CLZ) (.unop__case_0 _ _ _ rfl))
  | 0x7A => some (unary .I64 (.mk_unop__0 .I64 .CTZ) (.unop__case_0 _ _ _ rfl))
  | 0x7B => some (unary .I64 (.mk_unop__0 .I64 .POPCNT) (.unop__case_0 _ _ _ rfl))
  | 0x7C => some (binary .I64 (.mk_binop__0 .I64 (.ADD)) (.binop__case_0 _ _ _ rfl))
  | 0x7D => some (binary .I64 (.mk_binop__0 .I64 (.SUB)) (.binop__case_0 _ _ _ rfl))
  | 0x7E => some (binary .I64 (.mk_binop__0 .I64 (.MUL)) (.binop__case_0 _ _ _ rfl))
  | 0x7F => some (binary .I64 (.mk_binop__0 .I64 (.DIV .S)) (.binop__case_0 _ _ _ rfl))
  | 0x80 => some (binary .I64 (.mk_binop__0 .I64 (.DIV .U)) (.binop__case_0 _ _ _ rfl))
  | 0x81 => some (binary .I64 (.mk_binop__0 .I64 (.REM .S)) (.binop__case_0 _ _ _ rfl))
  | 0x82 => some (binary .I64 (.mk_binop__0 .I64 (.REM .U)) (.binop__case_0 _ _ _ rfl))
  | 0x83 => some (binary .I64 (.mk_binop__0 .I64 (.AND)) (.binop__case_0 _ _ _ rfl))
  | 0x84 => some (binary .I64 (.mk_binop__0 .I64 (.OR)) (.binop__case_0 _ _ _ rfl))
  | 0x85 => some (binary .I64 (.mk_binop__0 .I64 (.XOR)) (.binop__case_0 _ _ _ rfl))
  | 0x86 => some (binary .I64 (.mk_binop__0 .I64 (.SHL)) (.binop__case_0 _ _ _ rfl))
  | 0x87 => some (binary .I64 (.mk_binop__0 .I64 (.SHR .S)) (.binop__case_0 _ _ _ rfl))
  | 0x88 => some (binary .I64 (.mk_binop__0 .I64 (.SHR .U)) (.binop__case_0 _ _ _ rfl))
  | 0x89 => some (binary .I64 (.mk_binop__0 .I64 (.ROTL)) (.binop__case_0 _ _ _ rfl))
  | 0x8A => some (binary .I64 (.mk_binop__0 .I64 (.ROTR)) (.binop__case_0 _ _ _ rfl))
  | 0x8B => some (unary .F32 (.mk_unop__1 .F32 .ABS) (.unop__case_1 _ _ _ rfl))
  | 0x8C => some (unary .F32 (.mk_unop__1 .F32 .NEG) (.unop__case_1 _ _ _ rfl))
  | 0x8D => some (unary .F32 (.mk_unop__1 .F32 .CEIL) (.unop__case_1 _ _ _ rfl))
  | 0x8E => some (unary .F32 (.mk_unop__1 .F32 .FLOOR) (.unop__case_1 _ _ _ rfl))
  | 0x8F => some (unary .F32 (.mk_unop__1 .F32 .TRUNC) (.unop__case_1 _ _ _ rfl))
  | 0x90 => some (unary .F32 (.mk_unop__1 .F32 .NEAREST) (.unop__case_1 _ _ _ rfl))
  | 0x91 => some (unary .F32 (.mk_unop__1 .F32 .SQRT) (.unop__case_1 _ _ _ rfl))
  | 0x92 => some (binary .F32 (.mk_binop__1 .F32 .ADD) (.binop__case_1 _ _ _ rfl))
  | 0x93 => some (binary .F32 (.mk_binop__1 .F32 .SUB) (.binop__case_1 _ _ _ rfl))
  | 0x94 => some (binary .F32 (.mk_binop__1 .F32 .MUL) (.binop__case_1 _ _ _ rfl))
  | 0x95 => some (binary .F32 (.mk_binop__1 .F32 .DIV) (.binop__case_1 _ _ _ rfl))
  | 0x96 => some (binary .F32 (.mk_binop__1 .F32 .MIN) (.binop__case_1 _ _ _ rfl))
  | 0x97 => some (binary .F32 (.mk_binop__1 .F32 .MAX) (.binop__case_1 _ _ _ rfl))
  | 0x98 => some (binary .F32 (.mk_binop__1 .F32 .COPYSIGN) (.binop__case_1 _ _ _ rfl))
  | 0x99 => some (unary .F64 (.mk_unop__1 .F64 .ABS) (.unop__case_1 _ _ _ rfl))
  | 0x9A => some (unary .F64 (.mk_unop__1 .F64 .NEG) (.unop__case_1 _ _ _ rfl))
  | 0x9B => some (unary .F64 (.mk_unop__1 .F64 .CEIL) (.unop__case_1 _ _ _ rfl))
  | 0x9C => some (unary .F64 (.mk_unop__1 .F64 .FLOOR) (.unop__case_1 _ _ _ rfl))
  | 0x9D => some (unary .F64 (.mk_unop__1 .F64 .TRUNC) (.unop__case_1 _ _ _ rfl))
  | 0x9E => some (unary .F64 (.mk_unop__1 .F64 .NEAREST) (.unop__case_1 _ _ _ rfl))
  | 0x9F => some (unary .F64 (.mk_unop__1 .F64 .SQRT) (.unop__case_1 _ _ _ rfl))
  | 0xA0 => some (binary .F64 (.mk_binop__1 .F64 .ADD) (.binop__case_1 _ _ _ rfl))
  | 0xA1 => some (binary .F64 (.mk_binop__1 .F64 .SUB) (.binop__case_1 _ _ _ rfl))
  | 0xA2 => some (binary .F64 (.mk_binop__1 .F64 .MUL) (.binop__case_1 _ _ _ rfl))
  | 0xA3 => some (binary .F64 (.mk_binop__1 .F64 .DIV) (.binop__case_1 _ _ _ rfl))
  | 0xA4 => some (binary .F64 (.mk_binop__1 .F64 .MIN) (.binop__case_1 _ _ _ rfl))
  | 0xA5 => some (binary .F64 (.mk_binop__1 .F64 .MAX) (.binop__case_1 _ _ _ rfl))
  | 0xA6 => some (binary .F64 (.mk_binop__1 .F64 .COPYSIGN) (.binop__case_1 _ _ _ rfl))
  | 0xA7 => some (conversion .I64 .I32 (.mk_cvtop___0 .I64 .I32 (.WRAP)) (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_1 _ _ (by decide)) rfl rfl) (by decide))
  | 0xA8 => some (conversion .F32 .I32 (.mk_cvtop___2 .F32 .I32 (.TRUNC .S)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xA9 => some (conversion .F32 .I32 (.mk_cvtop___2 .F32 .I32 (.TRUNC .U)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xAA => some (conversion .F64 .I32 (.mk_cvtop___2 .F64 .I32 (.TRUNC .S)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xAB => some (conversion .F64 .I32 (.mk_cvtop___2 .F64 .I32 (.TRUNC .U)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xAC => some (conversion .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .S)) (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide))
  | 0xAD => some (conversion .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide))
  | 0xAE => some (conversion .F32 .I64 (.mk_cvtop___2 .F32 .I64 (.TRUNC .S)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xAF => some (conversion .F32 .I64 (.mk_cvtop___2 .F32 .I64 (.TRUNC .U)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB0 => some (conversion .F64 .I64 (.mk_cvtop___2 .F64 .I64 (.TRUNC .S)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB1 => some (conversion .F64 .I64 (.mk_cvtop___2 .F64 .I64 (.TRUNC .U)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB2 => some (conversion .I32 .F32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .S)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB3 => some (conversion .I32 .F32 (.mk_cvtop___1 .I32 .F32 (.CONVERT .U)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB4 => some (conversion .I64 .F32 (.mk_cvtop___1 .I64 .F32 (.CONVERT .S)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB5 => some (conversion .I64 .F32 (.mk_cvtop___1 .I64 .F32 (.CONVERT .U)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB6 => some (conversion .F64 .F32 (.mk_cvtop___3 .F64 .F32 (.DEMOTE)) (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide))
  | 0xB7 => some (conversion .I32 .F64 (.mk_cvtop___1 .I32 .F64 (.CONVERT .S)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB8 => some (conversion .I32 .F64 (.mk_cvtop___1 .I32 .F64 (.CONVERT .U)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xB9 => some (conversion .I64 .F64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .S)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xBA => some (conversion .I64 .F64 (.mk_cvtop___1 .I64 .F64 (.CONVERT .U)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_0 _ _ _) rfl rfl) (by decide))
  | 0xBB => some (conversion .F32 .F64 (.mk_cvtop___3 .F32 .F64 (.PROMOTE)) (.cvtop___case_3 _ _ _ _ _ (.cvtop__Fnn_1_Fnn_2_case_0 _ _ (by decide)) rfl rfl) (by decide))
  | 0xBC => some (conversion .F32 .I32 (.mk_cvtop___2 .F32 .I32 (.REINTERPRET)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl) (by decide))
  | 0xBD => some (conversion .F64 .I64 (.mk_cvtop___2 .F64 .I64 (.REINTERPRET)) (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_2 _ _ (by decide)) rfl rfl) (by decide))
  | 0xBE => some (conversion .I32 .F32 (.mk_cvtop___1 .I32 .F32 (.REINTERPRET)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide))
  | 0xBF => some (conversion .I64 .F64 (.mk_cvtop___1 .I64 .F64 (.REINTERPRET)) (.cvtop___case_1 _ _ _ _ _ (.cvtop__Inn_1_Fnn_2_case_1 _ _ (by decide)) rfl rfl) (by decide))
  | _ => none

/-- `op` is the numeric operation of the opcode. -/
def NumericOp (opcode : U8) (op : Operation) : Prop := opcodeMeaning opcode = some op

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Exactly the opcodes `0x45` to `0xbf` have a numeric meaning. -/
theorem opcodeMeaning_isSome (opcode : U8) :
    (opcodeMeaning opcode).isSome = decide (0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF) := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change n < 256 at hn
  interval_cases n <;> rfl

/-- Numeric opcodes lie between `0x45` and `0xbf`. -/
theorem NumericOp.bounds {opcode : U8} {op : Operation} (h : NumericOp opcode op) :
    0x45 ≤ opcode.val ∧ opcode.val ≤ 0xBF := by
  have hs := opcodeMeaning_isSome opcode
  rw [h] at hs
  simpa using hs.symm

end Itasca.Numeric

end

/-! ## Encoding -/

section

/-!
# Wasm 1.0 instruction binary grammar

The handwritten binary grammar of Wasm 1.0 instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, `TokenEncoding` adds the opcode, and `At` places a token in a byte
slice. `Consumed` accumulates the tokens read so far and `BodyEncoding` is a complete body,
including its final `end`. The `At.of_*` lemmas assemble tokens from decoded immediates. The
grammar does not mention validation: opcode meaning comes from the tables in
`Binary/Wasm1/NumericMeaning` and `Binary/Wasm1/MemoryMeaning`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

export Wasm2 (Token Simple Emits BodyTokens)

/-- `bytes` is the slice of `data` from `start` to `next`, followed by the untouched suffix. -/
structure BytesAt (data : Slice U8) (start : Usize) (bytes : List U8) (next : Usize) : Prop where
  suffix : data.val.drop start.val = bytes ++ data.val.drop next.val
  length : next.val = start.val + bytes.length
  bound : next.val ≤ data.length

/-- The concatenated unsigned LEB128 entries of an index vector, without the leading count. -/
inductive IndicesEncoding : List U32 → List U8 → Prop where
  | nil : IndicesEncoding [] []
  | cons {idx indices first rest} : Leb128.Encoding first idx.val →
      IndicesEncoding indices rest → IndicesEncoding (idx :: indices) (first ++ rest)

/-- The immediate bytes that follow an opcode byte for a Wasm 1.0 token. Literal opcode values,
the numeric and memory opcode tables and `ScalarBlockByte` define the accepted syntax. -/
inductive Immediate : U8 → Token → List U8 → Prop where
  | unreachable : Immediate 0x00#u8 (.plain .UNREACHABLE) []
  | nop : Immediate 0x01#u8 (.plain .NOP) []
  | block {bt b} : ScalarBlockByte bt b → Immediate 0x02#u8 (.block bt) [b]
  | loop {bt b} : ScalarBlockByte bt b → Immediate 0x03#u8 (.loop bt) [b]
  | if_ {bt b} : ScalarBlockByte bt b → Immediate 0x04#u8 (.if_ bt) [b]
  | else_ : Immediate 0x05#u8 .else_ []
  | end_ : Immediate 0x0B#u8 .end_ []
  | br (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x0C#u8 (.plain (.BR (.mk_uN idx.val))) bytes
  | brIf (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x0D#u8 (.plain (.BR_IF (.mk_uN idx.val))) bytes
  | brTable (indices : List U32) (default : U32) {count entries final} :
      Leb128.Encoding count indices.length → IndicesEncoding indices entries →
      Leb128.Encoding final default.val →
      Immediate 0x0E#u8 (.plain (.BR_TABLE (indices.map (fun i => .mk_uN i.val)) (.mk_uN default.val)))
        (count ++ entries ++ final)
  | return_ : Immediate 0x0F#u8 (.plain .RETURN) []
  | call (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x10#u8 (.plain (.CALL (.mk_uN idx.val))) bytes
  | callIndirect (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x11#u8 (.plain (.CALL_INDIRECT (.mk_uN 0) (.mk_uN idx.val))) (bytes ++ [0#u8])
  | drop : Immediate 0x1A#u8 (.plain .DROP) []
  | select : Immediate 0x1B#u8 (.plain (.SELECT none)) []
  | localGet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x20#u8 (.plain (.LOCAL_GET (.mk_uN idx.val))) bytes
  | localSet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x21#u8 (.plain (.LOCAL_SET (.mk_uN idx.val))) bytes
  | localTee (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x22#u8 (.plain (.LOCAL_TEE (.mk_uN idx.val))) bytes
  | globalGet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x23#u8 (.plain (.GLOBAL_GET (.mk_uN idx.val))) bytes
  | globalSet (idx : U32) {bytes} : Leb128.Encoding bytes idx.val →
      Immediate 0x24#u8 (.plain (.GLOBAL_SET (.mk_uN idx.val))) bytes
  | memory (opcode : U8) (operation : MemoryMeaning.Operation) (arg : code.MemArg)
      {alignment offset} (meaning : MemoryMeaning.opcodeMeaning opcode = some operation) :
      Leb128.Encoding alignment arg.align.val → Leb128.Encoding offset arg.offset.val →
      Immediate opcode (.plain (operation.op arg)) (alignment ++ offset)
  | memorySize : Immediate 0x3F#u8 (.plain .MEMORY_SIZE) [0#u8]
  | memoryGrow : Immediate 0x40#u8 (.plain .MEMORY_GROW) [0#u8]
  | i32Const (value : I32) {bytes} : SignedLeb32.Encoding bytes value.val →
      Immediate 0x41#u8 (.plain (Spec.i32Const value)) bytes
  | i64Const (value : I64) {bytes} : SignedLeb64.Encoding bytes value.val →
      Immediate 0x42#u8 (.plain (ScalarConst.i64 value)) bytes
  | f32Const (bits : U32) {bytes} : FloatBits.Encoding 4 bytes bits.val →
      Immediate 0x43#u8 (.plain (ScalarConst.f32 bits)) bytes
  | f64Const (bits : U64) {bytes} : FloatBits.Encoding 8 bytes bits.val →
      Immediate 0x44#u8 (.plain (ScalarConst.f64 bits)) bytes
  | numeric (opcode : U8) (operation : Numeric.Operation)
      (meaning : Numeric.opcodeMeaning opcode = some operation) :
      Immediate opcode (.plain operation.instruction) []

/-- A token as its opcode byte followed by its immediate bytes. -/
def TokenEncoding (token : Token) (bytes : List U8) : Prop :=
  ∃ opcode immediate, bytes = opcode :: immediate ∧ Immediate opcode token immediate

/-- A token is encoded by the interval from `start` to `next`. The suffix is unrestricted. -/
def At (data : Slice U8) (start : Usize) (token : Token) (next : Usize) : Prop :=
  ∃ bytes, TokenEncoding token bytes ∧ BytesAt data start bytes next

/-- The tokens read from `start` to the cursor, accumulated one `At` step at a time. -/
inductive Consumed (data : Slice U8) : Usize → List Token → Usize → Prop where
  | nil (pos : Usize) (bound : pos.val ≤ data.length) : Consumed data pos [] pos
  | snoc {start tokens pos token next} : Consumed data start tokens pos →
      At data pos token next → Consumed data start (tokens ++ [token]) next

/-- A complete function body: the tokens read from offset 0 reach the end of `data`, and end with
the final `end`. -/
def BodyEncoding (data : Slice U8) (ops : List instr) : Prop :=
  ∃ tokens next, Consumed data 0#usize tokens next ∧ next.val = data.length ∧ BodyTokens tokens ops

/-- The empty byte list occupies an empty interval at any cursor within the input. -/
theorem BytesAt.nil (data : Slice U8) (pos : Usize) (h : pos.val ≤ data.length) :
    BytesAt data pos [] pos := ⟨by simp, by simp, h⟩

/-- Adjacent byte intervals compose. -/
theorem BytesAt.append {data start middle next first rest}
    (hfirst : BytesAt data start first middle) (hrest : BytesAt data middle rest next) :
    BytesAt data start (first ++ rest) next := by
  refine ⟨?_, ?_, hrest.bound⟩
  · rw [hfirst.suffix, hrest.suffix, List.append_assoc]
  · simp only [List.length_append]
    have := hfirst.length
    have := hrest.length
    omega

/-- A single byte within the input occupies a one-byte interval. -/
theorem BytesAt.byte (data : Slice U8) (start next : Usize) (b : U8)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = b)
    (hnext : next.val = start.val + 1) : BytesAt data start [b] next := by
  refine ⟨?_, by simpa using hnext, by omega⟩
  rw [List.drop_eq_getElem_cons hstart, hbyte, hnext]
  rfl

/-- A token interval is nonempty and within the input. -/
theorem At.span {data start token next} (h : At data start token next) :
    start.val < next.val ∧ next.val ≤ data.length := by
  obtain ⟨_, ⟨op, imm, rfl, _⟩, hs⟩ := h
  have := hs.length
  simp only [List.length_cons] at this
  exact ⟨by omega, hs.bound⟩

/-- Composes an opcode byte with an immediate byte span. -/
theorem At.of_immediate {data start pos next opcode token immediate}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himmediate : Immediate opcode token immediate) (hspan : BytesAt data pos immediate next) :
    At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

/-- A token with no immediate bytes ends right after its opcode. -/
theorem At.no_immediate {data start next opcode token}
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hnext : next.val = start.val + 1) (himm : Immediate opcode token []) :
    At data start token next := by
  exact .of_immediate hstart hbyte hnext himm (.nil data next (by omega))

/-- Consumed spans compose. -/
theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

end Itasca.Wasm1

namespace Itasca.Wasm1

/-- Index vector entries compose. -/
theorem IndicesEncoding.append {first rest bs cs}
    (hfirst : IndicesEncoding first bs) (hrest : IndicesEncoding rest cs) :
    IndicesEncoding (first ++ rest) (bs ++ cs) := by
  induction hfirst with
  | nil => simpa using hrest
  | cons hb _ ih => simpa [List.append_assoc] using IndicesEncoding.cons hb ih

/-- Appending one entry to an index vector. -/
theorem IndicesEncoding.snoc {indices bytes idx last}
    (h : IndicesEncoding indices bytes) (hlast : Leb128.Encoding last idx.val) :
    IndicesEncoding (indices ++ [idx]) (bytes ++ last) := by
  simpa using h.append (.cons hlast .nil)

/-- A token whose immediate is a single unsigned LEB128 value, from a decoded `u32`. -/
theorem At.of_u32 {data start pos next opcode token} (value : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, Leb128.Encoding bytes value.val → Immediate opcode token bytes)
    (hdecoded : Leb128.Decoded data pos value next) : At data start token next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) ⟨hs, hl, hb⟩

/-- An `i32.const` token from a decoded signed 32-bit LEB128. -/
theorem At.of_s32 {data start pos next} (value : I32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x41#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : SignedLeb32.Decoded data pos value.val next) :
    At data start (.plain (Spec.i32Const value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i32Const value he) ⟨hs, hl, hb⟩

/-- An `i64.const` token from a decoded signed 64-bit LEB128. -/
theorem At.of_s64 {data start pos next} (value : I64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x42#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : SignedLeb64.Decoded data pos value.val next) :
    At data start (.plain (ScalarConst.i64 value)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.i64Const value he) ⟨hs, hl, hb⟩

/-- An `f32.const` token from four decoded bytes. -/
theorem At.of_f32 {data start pos next} (bits : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x43#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : FloatBits.Decoded 4 data pos bits.val next) :
    At data start (.plain (ScalarConst.f32 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f32Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- An `f64.const` token from eight decoded bytes. -/
theorem At.of_f64 {data start pos next} (bits : U64)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x44#u8)
    (hpos : pos.val = start.val + 1)
    (hdecoded : FloatBits.Decoded 8 data pos bits.val next) :
    At data start (.plain (ScalarConst.f64 bits)) next := by
  obtain ⟨bytes, hs, hl, hb, he⟩ := hdecoded
  exact .of_immediate hstart hbyte hpos (.f64Const bits he) ⟨hs, by rw [he.1]; exact hl, hb⟩

/-- A token whose immediate is a single byte, such as a block type or a reserved zero. -/
theorem At.of_byte {data : Slice U8} {start pos next : Usize} {opcode token} (immediate : U8)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (himm : Immediate opcode token [immediate])
    (hbound : pos.val < data.length) (hvalue : data.val[pos.val] = immediate)
    (hnext : next.val = pos.val + 1) : At data start token next := by
  exact .of_immediate hstart hbyte hpos himm (.byte data pos next immediate hbound hvalue hnext)

/-- A memory access token from a decoded alignment and offset. -/
theorem At.of_memory {data start pos middle next opcode} (operation : MemoryMeaning.Operation)
    (arg : code.MemArg) (meaning : MemoryMeaning.opcodeMeaning opcode = some operation)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1) (halign : Leb128.Decoded data pos arg.align middle)
    (hoffset : Leb128.Decoded data middle arg.offset next) :
    At data start (.plain (operation.op arg)) next := by
  obtain ⟨alignBytes, has, hal, hab, hae⟩ := halign
  obtain ⟨os, hos, hol, hob, hoe⟩ := hoffset
  exact .of_immediate hstart hbyte hpos (.memory opcode operation arg meaning hae hoe)
    ((show BytesAt data pos alignBytes middle from ⟨has, hal, hab⟩).append ⟨hos, hol, hob⟩)

end Itasca.Wasm1

end

/-! ## BrTableLabels -/

section

/-!
# Branch table immediates

Byte-level description of the `br_table` immediate: a count, that many labels and a default
label, each an unsigned LEB128. `BrTable.Decoded` describes it at a cursor, and
`Wasm1.At.of_br_table` and `Wasm1.At.of_table_decoded` assemble a `br_table` token from it.
-/

open Aeneas Aeneas.Std

namespace Itasca.BrTable

/-- A run of consecutive unsigned LEB128 labels decoded from the cursor. -/
inductive LabelsDecoded (data : Slice U8) (start : Usize) : List U32 → Usize → Prop where
  | nil : LabelsDecoded data start [] start
  | snoc {depths pos next depth} : LabelsDecoded data start depths pos →
      Leb128.Decoded data pos depth next → LabelsDecoded data start (depths ++ [depth]) next

/-- A label run stays within the input. -/
theorem LabelsDecoded.span {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil => exact ⟨le_rfl, hb⟩
  | snoc h hd ih =>
    have hs := hd.span
    omega

/-- The `br_table` immediate: a count, exactly that many labels and a default label. -/
def Decoded (data : Slice U8) (start : Usize) (depths : List U32)
    (default : U32) (next : Usize) : Prop :=
  ∃ count first last, Leb128.Decoded data start count first ∧
    depths.length = count.val ∧ LabelsDecoded data first depths last ∧
    Leb128.Decoded data last default next

/-- A label run has an `IndicesEncoding` over the bytes it occupies. -/
theorem LabelsDecoded.bytes {data start depths next}
    (h : LabelsDecoded data start depths next) (hb : start.val ≤ data.length) :
    ∃ bytes, Wasm1.IndicesEncoding depths bytes ∧ Wasm1.BytesAt data start bytes next := by
  induction h with
  | nil => exact ⟨[], .nil, .nil data start hb⟩
  | snoc _ hd ih =>
    obtain ⟨before, he, hs⟩ := ih
    obtain ⟨last, hlast, hlen, hbound, hencoding⟩ := hd
    exact ⟨before ++ last, he.snoc hencoding, hs.append ⟨hlast, hlen, hbound⟩⟩

end Itasca.BrTable

namespace Itasca.Wasm1

/-- A decoded count, label run and default label give a `br_table` token. -/
theorem At.of_br_table {data start pos first last next} (count : U32)
    (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hcount : Leb128.Decoded data pos count first)
    (hlen : depths.length = count.val) (hdepths : BrTable.LabelsDecoded data first depths last)
    (hdefault : Leb128.Decoded data last default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨countBytes, hc, hcl, hcb, hce⟩ := hcount
  obtain ⟨depthBytes, hde, hds⟩ := hdepths.bytes hcb
  obtain ⟨defaultBytes, hd, hdl, hdb, hde'⟩ := hdefault
  exact .of_immediate hstart hbyte hpos (.brTable depths default (by simpa [hlen] using hce) hde hde')
    (((show BytesAt data pos countBytes first from ⟨hc, hcl, hcb⟩).append hds).append ⟨hd, hdl, hdb⟩)

/-- A decoded `br_table` immediate gives a `br_table` token. -/
theorem At.of_table_decoded {data start pos next} (depths : List U32) (default : U32)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = 0x0E#u8)
    (hpos : pos.val = start.val + 1) (hdecoded : BrTable.Decoded data pos depths default next) :
    At data start (.plain (.BR_TABLE (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))) next := by
  obtain ⟨count, first, last, hc, hl, hd, hf⟩ := hdecoded
  exact .of_br_table count depths default hstart hbyte hpos hc hl hd hf

end Itasca.Wasm1

end

/-! ## EncodingComplete -/

section

/-!
# Reading Wasm 1.0 encodings

Splitting lemmas for `BytesAt`, `Consumed` and `BrTable.LabelsDecoded`, and lemmas that turn a
`BytesAt` span into a successful run of the extracted readers (`reader.read_u32_leb`,
`code.read_op`, `code.take_index`, `code.read_memarg`, ...).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm1

/-- A byte interval splits at any boundary of its bytes. -/
theorem BytesAt.split {data start next first rest}
    (h : BytesAt data start (first ++ rest) next) :
    ∃ middle, BytesAt data start first middle ∧ BytesAt data middle rest next := by
  have hlen := h.length
  simp only [List.length_append] at hlen
  let middle : Usize := Usize.ofNatCore (start.val + first.length)
    (by have := next.hmax; omega)
  have hm : middle.val = start.val + first.length := by simp [middle]
  have ht : data.val.drop middle.val = rest ++ data.val.drop next.val := by
    have hh := congrArg (List.drop first.length) h.suffix
    simpa [hm, List.drop_drop, List.drop_append, Nat.add_comm] using hh
  refine ⟨middle, ⟨?_, hm, by have := h.bound; omega⟩, ⟨ht, by omega, h.bound⟩⟩
  simpa [ht, List.append_assoc] using h.suffix

/-- An empty byte list occupies no input. -/
theorem BytesAt.empty {data start next} (h : BytesAt data start [] next) : next = start := by
  apply UScalar.eq_of_val_eq
  simpa using h.length

/-- A one-byte interval is the byte at the cursor. -/
theorem BytesAt.single {data start next byte} (h : BytesAt data start [byte] next) :
    ∃ hp : start.val < data.length, data.val[start.val] = byte ∧ next.val = start.val + 1 := by
  have hn : next.val = start.val + 1 := by simpa using h.length
  have hp : start.val < data.length := by have := h.bound; omega
  have hs := h.suffix
  rw [List.drop_eq_getElem_cons hp] at hs
  exact ⟨hp, (List.cons.inj hs).1, hn⟩

/-- `reader.read_byte` returns the byte of a one-byte interval. -/
theorem BytesAt.read_byte {data start next byte} (h : BytesAt data start [byte] next) :
    reader.read_byte data start = .ok (.Ok (byte, next)) := by
  obtain ⟨hp, hb, hn⟩ := h.single
  obtain ⟨_, hr, p, rfl, hp'⟩ := WP.spec_imp_exists (reader.read_byte.spec data start hp)
  have heq : p = next := UScalar.eq_of_val_eq (hp'.trans hn.symm)
  simpa [hb, heq] using hr

/-- A span with a `Leb128.Encoding` is a `Leb128.Decoded` span. -/
theorem BytesAt.u32_decoded {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Leb128.Encoding bytes value.val) :
    Leb128.Decoded data start value next := ⟨bytes, h.suffix, h.length, h.bound, he⟩

/-- `reader.read_u32_leb` reads an unsigned LEB128 span. -/
theorem BytesAt.read_u32 {data start next bytes} (value : U32)
    (h : BytesAt data start bytes next) (he : Leb128.Encoding bytes value.val) :
    reader.read_u32_leb data start = .ok (.Ok (value, next)) :=
  reader.read_u32_leb.complete data start value next (h.u32_decoded value he)

/-- `reader.read_f64_bits` reads an eight-byte span. -/
theorem BytesAt.read_f64 {data start next bytes} (bits : U64)
    (h : BytesAt data start bytes next) (he : FloatBits.Encoding 8 bytes bits.val) :
    reader.read_f64_bits data start = .ok (.Ok (bits, next)) :=
  reader.read_f64_bits.complete data start bits next
    ⟨bytes, h.suffix, by simpa [he.1] using h.length, h.bound, he⟩

/-- `code.take_index` reads an index span. -/
theorem BytesAt.take_index {data next bytes} (st : code.OpIterState) (idx : U32)
    (h : BytesAt data st.pos bytes next) (he : Leb128.Encoding bytes idx.val) :
    code.take_index st data = .ok (.Ok idx, { st with pos := next }) := by
  simp [code.take_index, h.read_u32 idx he, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.read_memarg` reads an alignment span followed by an offset span. -/
theorem BytesAt.read_memarg {data next alignment offset} (st : code.OpIterState)
    (arg : code.MemArg) (h : BytesAt data st.pos (alignment ++ offset) next)
    (ha : Leb128.Encoding alignment arg.align.val) (ho : Leb128.Encoding offset arg.offset.val) :
    code.read_memarg st data = .ok (.Ok arg, { st with pos := next }) := by
  obtain ⟨middle, hfirst, hrest⟩ := h.split
  have hr := hfirst.read_u32 arg.align ha
  have hr' := hrest.read_u32 arg.offset ho
  cases arg
  simp_all [code.read_memarg, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Wasm1

namespace Itasca.BrTable

/-- Label runs compose. -/
theorem LabelsDecoded.append {data start middle next first rest}
    (hfirst : LabelsDecoded data start first middle)
    (hrest : LabelsDecoded data middle rest next) :
    LabelsDecoded data start (first ++ rest) next := by
  induction hrest with
  | nil => simpa using hfirst
  | snoc _ hd ih => simpa [List.append_assoc] using LabelsDecoded.snoc ih hd

private theorem labels_split {data start depths next} (h : LabelsDecoded data start depths next)
    (first rest : List U32) (heq : depths = first ++ rest) :
    ∃ middle, LabelsDecoded data start first middle ∧ LabelsDecoded data middle rest next := by
  induction h generalizing first rest with
  | nil =>
      have he : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases he with ⟨rfl, rfl⟩
      exact ⟨start, .nil, .nil⟩
  | @snoc depths pos next depth hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = depths ++ [depth] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil⟩
      | append_singleton rest last =>
          have heq' : depths ++ [depth] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : depth = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          obtain ⟨middle, hf, hr⟩ := ih first rest (List.append_cancel_right heq')
          exact ⟨middle, hf, .snoc hr hlast⟩

private theorem labels_empty {data start depths next}
    (h : LabelsDecoded data start depths next) (he : depths = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

private theorem labels_single {data start next depth}
    (h : LabelsDecoded data start [depth] next) : Leb128.Decoded data start depth next := by
  generalize he : [depth] = depths at h
  cases h with
  | nil => simp at he
  | @snoc depths pos next last hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : depths = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = depth := by simpa [ht] using he.symm
      have hpos := labels_empty hp ht
      simpa [heq, hpos] using hl

/-- A nonempty label run is its first label followed by the rest. -/
theorem LabelsDecoded.cons_iff {data start next depth depths} :
    LabelsDecoded data start (depth :: depths) next ↔
      ∃ middle, Leb128.Decoded data start depth middle ∧ LabelsDecoded data middle depths next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := labels_split h [depth] depths rfl
    exact ⟨middle, labels_single hh, ht⟩
  · rintro ⟨middle, hh, ht⟩
    exact LabelsDecoded.append (.snoc .nil hh) ht

end Itasca.BrTable

namespace Itasca.Wasm1

/-- An `IndicesEncoding` over a byte span gives a run of decoded labels. -/
theorem IndicesEncoding.decoded {indices bytes} (he : IndicesEncoding indices bytes)
    {data start next} (h : BytesAt data start bytes next) :
    BrTable.LabelsDecoded data start indices next := by
  induction he generalizing start with
  | nil => have hn := h.empty; subst next; exact .nil
  | cons hidx _ ih =>
      obtain ⟨middle, hfirst, hrest⟩ := h.split
      have hhead := BrTable.LabelsDecoded.snoc .nil (hfirst.u32_decoded _ hidx)
      simpa using hhead.append (ih hrest)

/-- The count, entries and default label of a `br_table` immediate give a `BrTable.Decoded`. The
count's `u32` range follows from its own encoding. -/
theorem BytesAt.br_table_decoded {data start next count entries final}
    (indices : List U32) (default : U32)
    (h : BytesAt data start (count ++ entries ++ final) next)
    (hc : Leb128.Encoding count indices.length) (he : IndicesEncoding indices entries)
    (hf : Leb128.Encoding final default.val) :
    BrTable.Decoded data start indices default next := by
  obtain ⟨last, hprefix, hfinal⟩ := h.split
  obtain ⟨first, hcount, hentries⟩ := hprefix.split
  let n : U32 := U32.ofNatCore indices.length (by simpa using hc.value_lt)
  have hn : n.val = indices.length := by simp [n]
  exact ⟨n, first, last, hcount.u32_decoded n (by simpa [hn] using hc), hn.symm,
    he.decoded hentries, hfinal.u32_decoded default hf⟩

/-- A consumed span splits at any token boundary. -/
theorem Consumed.split_eq {data start tokens next} (h : Consumed data start tokens next)
    (first rest : List Token) (heq : tokens = first ++ rest) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next := by
  induction h generalizing first rest with
  | nil hb =>
      have hempty : first = [] ∧ rest = [] := by simpa using heq.symm
      rcases hempty with ⟨rfl, rfl⟩
      exact ⟨start, .nil start hb, .nil start hb⟩
  | @snoc tokens pos token next hprefix hlast ih =>
      cases rest using List.reverseRecOn with
      | nil =>
          have hf : first = tokens ++ [token] := by simpa using heq.symm
          subst first
          exact ⟨next, .snoc hprefix hlast, .nil next hlast.span.2⟩
      | append_singleton rest last =>
          have heq' : tokens ++ [token] = (first ++ rest) ++ [last] := by
            simpa [List.append_assoc] using heq
          have ht : token = last := by
            have := congrArg List.getLast? heq'
            simpa using this
          subst last
          have hp : tokens = first ++ rest := List.append_cancel_right heq'
          obtain ⟨middle, hf, hr⟩ := ih first rest hp
          exact ⟨middle, hf, .snoc hr hlast⟩

/-- A consumed span of a concatenation splits into consecutive spans. -/
theorem Consumed.split {data start next first rest}
    (h : Consumed data start (first ++ rest) next) :
    ∃ middle, Consumed data start first middle ∧ Consumed data middle rest next :=
  h.split_eq first rest rfl

/-- An empty token list leaves the cursor in place. -/
theorem Consumed.empty_eq {data start tokens next}
    (h : Consumed data start tokens next) (he : tokens = []) : next = start := by
  cases h with
  | nil => rfl
  | snoc => simp at he

/-- A consumed span of one token is an `At`. -/
theorem Consumed.single {data start next token}
    (h : Consumed data start [token] next) : At data start token next := by
  generalize he : [token] = tokens at h
  cases h with
  | nil => simp at he
  | @snoc tokens pos last next hp hl =>
      have hlen := congrArg List.length he
      simp only [List.length_cons, List.length_nil, List.length_append] at hlen
      have ht : tokens = [] := List.length_eq_zero_iff.mp (by omega)
      have heq : last = token := by simpa [ht] using he.symm
      have hpos := hp.empty_eq ht
      simpa [heq, hpos] using hl

/-- A nonempty consumed span is its first token followed by the rest. -/
theorem Consumed.cons_iff {data start next token tokens} :
    Consumed data start (token :: tokens) next ↔
      ∃ middle, At data start token middle ∧ Consumed data middle tokens next := by
  constructor
  · intro h
    obtain ⟨middle, hh, ht⟩ := h.split_eq [token] tokens rfl
    exact ⟨middle, hh.single, ht⟩
  · rintro ⟨middle, hh, ht⟩
    have hb : start.val ≤ data.length := by have := hh.span; omega
    exact Consumed.append (.snoc (.nil start hb) hh) ht

end Itasca.Wasm1

namespace Itasca.Wasm1

end Itasca.Wasm1

end
