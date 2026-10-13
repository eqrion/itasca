import Itasca.Binary.Wasm1.NumericMeaning
import Itasca.Spec.DeclaredReferences

/-!
# Wasm 2.0 numeric additions

The sign-extension opcodes `0xc0` to `0xc4` and the saturating truncation subopcodes 0 to 7 under
`0xfc`, as `Numeric.Operation` rows (`signMeaning`, `saturatingMeaning`). Each row carries a
proof that it is well formed and typed by `Instr_ok`. `sign_signature` and `saturating_signature`
recover the stack effect from a generated typing, and `sign_declared` and `saturating_declared`
show that the rows carry no `ref.func`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.NumericExtensions

/-- The `i32.extend8_s` operation. -/
def i32Extend8 : Numeric.Operation where
  instruction := .UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 8))
  input := .I32
  output := .I32
  binary := false
  wellFormed := .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.unop C .I32
      (.mk_unop__0 .I32 (.EXTEND 8)) hC (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))

/-- The `i32.extend16_s` operation. -/
def i32Extend16 : Numeric.Operation where
  instruction := .UNOP .I32 (.mk_unop__0 .I32 (.EXTEND 16))
  input := .I32
  output := .I32
  binary := false
  wellFormed := .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.unop C .I32
      (.mk_unop__0 .I32 (.EXTEND 16)) hC (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))

/-- The `i64.extend8_s` operation. -/
def i64Extend8 : Numeric.Operation where
  instruction := .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 8))
  input := .I64
  output := .I64
  binary := false
  wellFormed := .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.unop C .I64
      (.mk_unop__0 .I64 (.EXTEND 8)) hC (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))

/-- The `i64.extend16_s` operation. -/
def i64Extend16 : Numeric.Operation where
  instruction := .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 16))
  input := .I64
  output := .I64
  binary := false
  wellFormed := .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.unop C .I64
      (.mk_unop__0 .I64 (.EXTEND 16)) hC (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))

/-- The `i64.extend32_s` operation. -/
def i64Extend32 : Numeric.Operation where
  instruction := .UNOP .I64 (.mk_unop__0 .I64 (.EXTEND 32))
  input := .I64
  output := .I64
  binary := false
  wellFormed := .instr_case_14 _ _ (.unop__case_0 _ _ _ rfl)
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.unop C .I64
      (.mk_unop__0 .I64 (.EXTEND 32)) hC (.instr_case_14 _ _ (.unop__case_0 _ _ _ rfl))

/-- The `i32.trunc_sat_f32_s` operation. -/
def i32TruncSatF32S : Numeric.Operation where
  instruction := .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .S))
  input := .F32
  output := .I32
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I32 .F32
      (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .S)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i32.trunc_sat_f32_u` operation. -/
def i32TruncSatF32U : Numeric.Operation where
  instruction := .CVTOP .I32 .F32 (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .U))
  input := .F32
  output := .I32
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I32 .F32
      (.mk_cvtop___2 .F32 .I32 (.TRUNC_SAT .U)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i32.trunc_sat_f64_s` operation. -/
def i32TruncSatF64S : Numeric.Operation where
  instruction := .CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .S))
  input := .F64
  output := .I32
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I32 .F64
      (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .S)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i32.trunc_sat_f64_u` operation. -/
def i32TruncSatF64U : Numeric.Operation where
  instruction := .CVTOP .I32 .F64 (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .U))
  input := .F64
  output := .I32
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I32 .F64
      (.mk_cvtop___2 .F64 .I32 (.TRUNC_SAT .U)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i64.trunc_sat_f32_s` operation. -/
def i64TruncSatF32S : Numeric.Operation where
  instruction := .CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .S))
  input := .F32
  output := .I64
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I64 .F32
      (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .S)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i64.trunc_sat_f32_u` operation. -/
def i64TruncSatF32U : Numeric.Operation where
  instruction := .CVTOP .I64 .F32 (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .U))
  input := .F32
  output := .I64
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I64 .F32
      (.mk_cvtop___2 .F32 .I64 (.TRUNC_SAT .U)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i64.trunc_sat_f64_s` operation. -/
def i64TruncSatF64S : Numeric.Operation where
  instruction := .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .S))
  input := .F64
  output := .I64
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I64 .F64
      (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .S)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The `i64.trunc_sat_f64_u` operation. -/
def i64TruncSatF64U : Numeric.Operation where
  instruction := .CVTOP .I64 .F64 (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .U))
  input := .F64
  output := .I64
  binary := false
  wellFormed := (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))
  typed C hC := by
    simpa [Translate.valueType, valtype_numtype] using Instr_ok.cvtop C .I64 .F64
      (.mk_cvtop___2 .F64 .I64 (.TRUNC_SAT .U)) hC (.instr_case_18 _ _ _ (.cvtop___case_2 _ _ _ _ _ (.cvtop__Fnn_1_Inn_2_case_1 _ _ _) rfl rfl) (by decide))

/-- The single-byte sign-extension opcodes `0xc0` to `0xc4`. -/
def signMeaning (opcode : U8) : Option Numeric.Operation :=
  match opcode.val with
  | 0xC0 => some i32Extend8
  | 0xC1 => some i32Extend16
  | 0xC2 => some i64Extend8
  | 0xC3 => some i64Extend16
  | 0xC4 => some i64Extend32
  | _ => none

/-- The eight saturating truncation subopcodes under the `0xfc` prefix. -/
def saturatingMeaning (opcode : U32) : Option Numeric.Operation :=
  match opcode.val with
  | 0 => some i32TruncSatF32S
  | 1 => some i32TruncSatF32U
  | 2 => some i32TruncSatF64S
  | 3 => some i32TruncSatF64U
  | 4 => some i64TruncSatF32S
  | 5 => some i64TruncSatF32U
  | 6 => some i64TruncSatF64S
  | 7 => some i64TruncSatF64U
  | _ => none


/-- A generated typing of a sign-extension row has the row's stack effect. -/
theorem sign_signature {opcode op} (hmap : signMeaning opcode = some op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translate.valueType ∧ outs = [Translate.valueType op.output] := by
  unfold signMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; cases ht; exact ⟨rfl, rfl⟩

/-- A generated typing of a saturating truncation row has the row's stack effect. -/
theorem saturating_signature {opcode op} (hmap : saturatingMeaning opcode = some op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translate.valueType ∧ outs = [Translate.valueType op.output] := by
  unfold saturatingMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; cases ht; exact ⟨rfl, rfl⟩

/-- Sign-extension rows have no declared-reference obligation. -/
theorem sign_declared {opcode op} (hmap : signMeaning opcode = some op) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.instruction := by
  unfold signMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; simp [i32Extend8, i32Extend16, i64Extend8, i64Extend16, i64Extend32,
    DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

/-- Saturating truncation rows have no declared-reference obligation. -/
theorem saturating_declared {opcode op} (hmap : saturatingMeaning opcode = some op) (refs : List funcidx) :
    DeclaredReferences.Instruction refs op.instruction := by
  unfold saturatingMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; simp [i32TruncSatF32S, i32TruncSatF32U, i32TruncSatF64S, i32TruncSatF64U,
    i64TruncSatF32S, i64TruncSatF32U, i64TruncSatF64S, i64TruncSatF64U,
    DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]


end Itasca.Wasm2.NumericExtensions
