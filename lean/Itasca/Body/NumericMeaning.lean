import Itasca.Support.TypeTranslation

open Aeneas Aeneas.Std

namespace Itasca.Numeric

/-- The scalar numeric type used by the independent specification map. -/
def numType : types.ValueType → numtype
  | .I32 => .I32
  | .I64 => .I64
  | .F32 => .F32
  | .F64 => .F64

@[simp] theorem numType_value (t : types.ValueType) :
    valtype_numtype (numType t) = Translate.valueType t := by cases t <;> rfl

/-- A scalar instruction together with its one- or two-operand specification effect. -/
structure Operation where
  instruction : instr
  input : types.ValueType
  output : types.ValueType
  binary : Bool
  wellFormed : wf_instr instruction
  typed : ∀ C, wf_context C → Instr_ok C instruction
    (.mk_functype (.mk_list ((if binary then [input, input] else [input]).map Translate.valueType))
      (.mk_list [Translate.valueType output]))

def Operation.inputs (op : Operation) : List types.ValueType :=
  if op.binary then [op.input, op.input] else [op.input]

def unary (t : types.ValueType) (op : unop_) (hwf : wf_unop_ (numType t) op) : Operation where
  instruction := .UNOP (numType t) op
  input := t
  output := t
  binary := false
  wellFormed := .instr_case_14 _ _ hwf
  typed C hC := by simpa using Instr_ok.unop C (numType t) op hC (.instr_case_14 _ _ hwf)

def binary (t : types.ValueType) (op : binop_) (hwf : wf_binop_ (numType t) op) : Operation where
  instruction := .BINOP (numType t) op
  input := t
  output := t
  binary := true
  wellFormed := .instr_case_15 _ _ hwf
  typed C hC := by simpa using Instr_ok.binop C (numType t) op hC (.instr_case_15 _ _ hwf)

def test (t : types.ValueType) (op : testop_) (hwf : wf_testop_ (numType t) op) : Operation where
  instruction := .TESTOP (numType t) op
  input := t
  output := .I32
  binary := false
  wellFormed := .instr_case_16 _ _ hwf
  typed C hC := by simpa [Translate.valueType] using Instr_ok.testop C (numType t) op hC (.instr_case_16 _ _ hwf)

def relation (t : types.ValueType) (op : relop_) (hwf : wf_relop_ (numType t) op) : Operation where
  instruction := .RELOP (numType t) op
  input := t
  output := .I32
  binary := true
  wellFormed := .instr_case_17 _ _ hwf
  typed C hC := by simpa [Translate.valueType] using Instr_ok.relop C (numType t) op hC (.instr_case_17 _ _ hwf)

def conversion (source target : types.ValueType) (op : cvtop__)
    (hwf : wf_cvtop__ (numType source) (numType target) op)
    (hne : numType target ≠ numType source) : Operation where
  instruction := .CVTOP (numType target) (numType source) op
  input := source
  output := target
  binary := false
  wellFormed := .instr_case_18 _ _ _ hwf hne
  typed C hC := by
    simpa using Instr_ok.cvtop C (numType target) (numType source) op hC
      (.instr_case_18 _ _ _ hwf hne)

/-- The WebAssembly 1.0 scalar numeric opcode table, specified independently of the validator tables. -/
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

def NumericOp (opcode : U8) (op : Operation) : Prop := opcodeMeaning opcode = some op

end Itasca.Numeric
