import Aeneas
import «wasm2.0»
import Itasca.Spec.DeclaredReferences

/-!
# Wasm 2.0 SIMD instructions without immediates

`Simd.pureMeaning` is a literal table from the `0xfd` subopcodes of SIMD instructions that take no
immediate to `Simd.Operation` rows. Each row (`pure14`, `pure15`, ...) holds the SpecTec
instruction, its stack signature and proofs that it is well formed, typed by `Instr_ok` with that
signature, free of `ref.func`, and that the generated typing is principal. `pure_signature` and
`pure_bound` are the table-level consequences. The table is written independently of the extracted
opcode dispatch.
-/

namespace Itasca.Wasm2.Simd

/-- The stack signature shapes of the SIMD instructions without immediates. -/
inductive Signature where
  | unary | binary | ternary | test | shift
  | splatI32 | splatI64 | splatF32 | splatF64

/-- The operand types of a signature. -/
def Signature.inputs : Signature → List valtype
  | .unary | .test => [.V128]
  | .binary => [.V128, .V128]
  | .ternary => [.V128, .V128, .V128]
  | .shift => [.V128, .I32]
  | .splatI32 => [.I32]
  | .splatI64 => [.I64]
  | .splatF32 => [.F32]
  | .splatF64 => [.F64]

/-- The result types of a signature. -/
def Signature.outputs : Signature → List valtype
  | .test => [.I32]
  | _ => [.V128]

private theorem integer8_wf : wf_ishape (.mk_ishape (.X .I8 (.mk_dim 16))) := by
  apply wf_ishape.ishape_case_0 .I8
  · repeat' first | decide | constructor
  · rfl

private theorem integer16_wf : wf_ishape (.mk_ishape (.X .I16 (.mk_dim 8))) := by
  apply wf_ishape.ishape_case_0 .I16
  · repeat' first | decide | constructor
  · rfl

private theorem integer32_wf : wf_ishape (.mk_ishape (.X .I32 (.mk_dim 4))) := by
  apply wf_ishape.ishape_case_0 .I32
  · repeat' first | decide | constructor
  · rfl

private theorem integer64_wf : wf_ishape (.mk_ishape (.X .I64 (.mk_dim 2))) := by
  apply wf_ishape.ishape_case_0 .I64
  · repeat' first | decide | constructor
  · rfl

/-- A SIMD instruction without immediates with its signature, and proofs that it is well formed,
typed with that signature, free of declared-reference obligations, and that the signature is the
only one the generated rules give it. -/
structure Operation where
  instruction : instr
  signature : Signature
  wellFormed : wf_instr instruction
  typed : ∀ C, wf_context C → Instr_ok C instruction
    (.mk_functype (.mk_list signature.inputs) (.mk_list signature.outputs))
  declared : ∀ refs, DeclaredReferences.Instruction refs instruction
  principal : ∀ C ins outs, Instr_ok C instruction (.mk_functype (.mk_list ins) (.mk_list outs)) →
    ins = signature.inputs ∧ outs = signature.outputs

/-- `VSWIZZLE (I8 X 16)`. -/
def pure14 : Operation :=
  let instruction : instr := .VSWIZZLE (.mk_ishape (.X .I8 (.mk_dim 16)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vswizzle C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (I8 X 16)`. -/
def pure15 : Operation :=
  let instruction : instr := .VSPLAT (.X .I8 (.mk_dim 16))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatI32, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (I16 X 8)`. -/
def pure16 : Operation :=
  let instruction : instr := .VSPLAT (.X .I16 (.mk_dim 8))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatI32, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (I32 X 4)`. -/
def pure17 : Operation :=
  let instruction : instr := .VSPLAT (.X .I32 (.mk_dim 4))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatI32, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (I64 X 2)`. -/
def pure18 : Operation :=
  let instruction : instr := .VSPLAT (.X .I64 (.mk_dim 2))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatI64, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (F32 X 4)`. -/
def pure19 : Operation :=
  let instruction : instr := .VSPLAT (.X .F32 (.mk_dim 4))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatF32, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSPLAT (F64 X 2)`. -/
def pure20 : Operation :=
  let instruction : instr := .VSPLAT (.X .F64 (.mk_dim 2))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .splatF64, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vsplat C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) EQ`. -/
def pure35 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) NE`. -/
def pure36 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (LT S)`. -/
def pure37 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (LT U)`. -/
def pure38 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (GT S)`. -/
def pure39 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (GT U)`. -/
def pure40 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (LE S)`. -/
def pure41 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (LE U)`. -/
def pure42 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.LE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (GE S)`. -/
def pure43 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I8 X 16) (GE U)`. -/
def pure44 : Operation :=
  let instruction : instr := .VRELOP (.X .I8 (.mk_dim 16)) (.mk_vrelop__0 .I8 16 (.GE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) EQ`. -/
def pure45 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) NE`. -/
def pure46 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (LT S)`. -/
def pure47 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (LT U)`. -/
def pure48 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (GT S)`. -/
def pure49 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (GT U)`. -/
def pure50 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (LE S)`. -/
def pure51 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (LE U)`. -/
def pure52 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.LE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (GE S)`. -/
def pure53 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I16 X 8) (GE U)`. -/
def pure54 : Operation :=
  let instruction : instr := .VRELOP (.X .I16 (.mk_dim 8)) (.mk_vrelop__0 .I16 8 (.GE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) EQ`. -/
def pure55 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) NE`. -/
def pure56 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (LT S)`. -/
def pure57 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (LT U)`. -/
def pure58 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (GT S)`. -/
def pure59 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (GT U)`. -/
def pure60 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (LE S)`. -/
def pure61 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (LE U)`. -/
def pure62 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.LE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (GE S)`. -/
def pure63 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I32 X 4) (GE U)`. -/
def pure64 : Operation :=
  let instruction : instr := .VRELOP (.X .I32 (.mk_dim 4)) (.mk_vrelop__0 .I32 4 (.GE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) EQ`. -/
def pure65 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) NE`. -/
def pure66 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) LT`. -/
def pure67 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) GT`. -/
def pure68 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) LE`. -/
def pure69 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .LE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F32 X 4) GE`. -/
def pure70 : Operation :=
  let instruction : instr := .VRELOP (.X .F32 (.mk_dim 4)) (.mk_vrelop__1 .F32 4 .GE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) EQ`. -/
def pure71 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) NE`. -/
def pure72 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) LT`. -/
def pure73 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) GT`. -/
def pure74 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) LE`. -/
def pure75 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .LE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (F64 X 2) GE`. -/
def pure76 : Operation :=
  let instruction : instr := .VRELOP (.X .F64 (.mk_dim 2)) (.mk_vrelop__1 .F64 2 .GE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVUNOP V128 NOT`. -/
def pure77 : Operation :=
  let instruction : instr := .VVUNOP .V128 .NOT
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvunop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVBINOP V128 AND`. -/
def pure78 : Operation :=
  let instruction : instr := .VVBINOP .V128 .AND
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvbinop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVBINOP V128 ANDNOT`. -/
def pure79 : Operation :=
  let instruction : instr := .VVBINOP .V128 .ANDNOT
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvbinop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVBINOP V128 OR`. -/
def pure80 : Operation :=
  let instruction : instr := .VVBINOP .V128 .OR
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvbinop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVBINOP V128 XOR`. -/
def pure81 : Operation :=
  let instruction : instr := .VVBINOP .V128 .XOR
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvbinop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVTERNOP V128 BITSELECT`. -/
def pure82 : Operation :=
  let instruction : instr := .VVTERNOP .V128 .BITSELECT
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .ternary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvternop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VVTESTOP V128 ANY_TRUE`. -/
def pure83 : Operation :=
  let instruction : instr := .VVTESTOP .V128 .ANY_TRUE
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vvtestop C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F32 X 4) (F64 X 2) DEMOTE ZERO`. -/
def pure94 : Operation :=
  let instruction : instr := .VCVTOP (.X .F32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___3 .F64 2 .F32 4 (.DEMOTE .ZERO))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F64 X 2) (F32 X 4) PROMOTE LOW`. -/
def pure95 : Operation :=
  let instruction : instr := .VCVTOP (.X .F64 (.mk_dim 2)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___3 .F32 4 .F64 2 .PROMOTELOW)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I8 X 16) ABS`. -/
def pure96 : Operation :=
  let instruction : instr := .VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I8 X 16) NEG`. -/
def pure97 : Operation :=
  let instruction : instr := .VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I8 X 16) POPCNT`. -/
def pure98 : Operation :=
  let instruction : instr := .VUNOP (.X .I8 (.mk_dim 16)) (.mk_vunop__0 .I8 16 .POPCNT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VTESTOP (I8 X 16) ALL_TRUE`. -/
def pure99 : Operation :=
  let instruction : instr := .VTESTOP (.X .I8 (.mk_dim 16)) (.mk_vtestop__0 .I8 16 .ALL_TRUE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vtestop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBITMASK (I8 X 16)`. -/
def pure100 : Operation :=
  let instruction : instr := .VBITMASK (.mk_ishape (.X .I8 (.mk_dim 16)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbitmask C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VNARROW (I8 X 16) (I16 X 8) S`. -/
def pure101 : Operation :=
  let instruction : instr := .VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .S
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vnarrow C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VNARROW (I8 X 16) (I16 X 8) U`. -/
def pure102 : Operation :=
  let instruction : instr := .VNARROW (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_ishape (.X .I16 (.mk_dim 8))) .U
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vnarrow C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) CEIL`. -/
def pure103 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .CEIL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) FLOOR`. -/
def pure104 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .FLOOR)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) TRUNC`. -/
def pure105 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .TRUNC)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) NEAREST`. -/
def pure106 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEAREST)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I8 X 16) SHL`. -/
def pure107 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 .SHL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I8 X 16) (SHR S)`. -/
def pure108 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I8 X 16) (SHR U)`. -/
def pure109 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vshiftop__0 .I8 16 (.SHR .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) ADD`. -/
def pure110 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (ADD_SAT S)`. -/
def pure111 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (ADD_SAT U)`. -/
def pure112 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.ADD_SAT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) SUB`. -/
def pure113 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (SUB_SAT S)`. -/
def pure114 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (SUB_SAT U)`. -/
def pure115 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.SUB_SAT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) CEIL`. -/
def pure116 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .CEIL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) FLOOR`. -/
def pure117 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .FLOOR)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (MIN S)`. -/
def pure118 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (MIN U)`. -/
def pure119 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MIN .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (MAX S)`. -/
def pure120 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (MAX U)`. -/
def pure121 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 (.MAX .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) TRUNC`. -/
def pure122 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .TRUNC)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I8 X 16) (AVGR U)`. -/
def pure123 : Operation :=
  let instruction : instr := .VBINOP (.X .I8 (.mk_dim 16)) (.mk_vbinop__0 .I8 16 .AVGRU)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTUNOP (I16 X 8) (I8 X 16) (EXTADD_PAIRWISE S)`. -/
def pure124 : Operation :=
  let instruction : instr := .VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextunop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTUNOP (I16 X 8) (I8 X 16) (EXTADD_PAIRWISE U)`. -/
def pure125 : Operation :=
  let instruction : instr := .VEXTUNOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextunop___0 .I8 16 .I16 8 (.EXTADD_PAIRWISE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextunop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTUNOP (I32 X 4) (I16 X 8) (EXTADD_PAIRWISE S)`. -/
def pure126 : Operation :=
  let instruction : instr := .VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextunop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTUNOP (I32 X 4) (I16 X 8) (EXTADD_PAIRWISE U)`. -/
def pure127 : Operation :=
  let instruction : instr := .VEXTUNOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextunop___0 .I16 8 .I32 4 (.EXTADD_PAIRWISE .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextunop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I16 X 8) ABS`. -/
def pure128 : Operation :=
  let instruction : instr := .VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I16 X 8) NEG`. -/
def pure129 : Operation :=
  let instruction : instr := .VUNOP (.X .I16 (.mk_dim 8)) (.mk_vunop__0 .I16 8 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (Q15MULR_SAT S)`. -/
def pure130 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .Q15MULR_SATS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VTESTOP (I16 X 8) ALL_TRUE`. -/
def pure131 : Operation :=
  let instruction : instr := .VTESTOP (.X .I16 (.mk_dim 8)) (.mk_vtestop__0 .I16 8 .ALL_TRUE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vtestop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBITMASK (I16 X 8)`. -/
def pure132 : Operation :=
  let instruction : instr := .VBITMASK (.mk_ishape (.X .I16 (.mk_dim 8)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbitmask C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VNARROW (I16 X 8) (I32 X 4) S`. -/
def pure133 : Operation :=
  let instruction : instr := .VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .S
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vnarrow C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VNARROW (I16 X 8) (I32 X 4) U`. -/
def pure134 : Operation :=
  let instruction : instr := .VNARROW (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I32 (.mk_dim 4))) .U
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vnarrow C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I16 X 8) (I8 X 16) (EXTEND LOW S)`. -/
def pure135 : Operation :=
  let instruction : instr := .VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I16 X 8) (I8 X 16) (EXTEND HIGH S)`. -/
def pure136 : Operation :=
  let instruction : instr := .VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I16 X 8) (I8 X 16) (EXTEND LOW U)`. -/
def pure137 : Operation :=
  let instruction : instr := .VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I16 X 8) (I8 X 16) (EXTEND HIGH U)`. -/
def pure138 : Operation :=
  let instruction : instr := .VCVTOP (.X .I16 (.mk_dim 8)) (.X .I8 (.mk_dim 16)) (.mk_vcvtop___0 .I8 16 .I16 8 (.EXTEND .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I16 X 8) SHL`. -/
def pure139 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 .SHL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I16 X 8) (SHR S)`. -/
def pure140 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I16 X 8) (SHR U)`. -/
def pure141 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vshiftop__0 .I16 8 (.SHR .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) ADD`. -/
def pure142 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (ADD_SAT S)`. -/
def pure143 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (ADD_SAT U)`. -/
def pure144 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.ADD_SAT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) SUB`. -/
def pure145 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (SUB_SAT S)`. -/
def pure146 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (SUB_SAT U)`. -/
def pure147 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.SUB_SAT .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) NEAREST`. -/
def pure148 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEAREST)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) MUL`. -/
def pure149 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .MUL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (MIN S)`. -/
def pure150 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (MIN U)`. -/
def pure151 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MIN .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (MAX S)`. -/
def pure152 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (MAX U)`. -/
def pure153 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 (.MAX .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I16 X 8) (AVGR U)`. -/
def pure155 : Operation :=
  let instruction : instr := .VBINOP (.X .I16 (.mk_dim 8)) (.mk_vbinop__0 .I16 8 .AVGRU)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I16 X 8) (I8 X 16) (EXTMUL LOW S)`. -/
def pure156 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I16 X 8) (I8 X 16) (EXTMUL HIGH S)`. -/
def pure157 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I16 X 8) (I8 X 16) (EXTMUL LOW U)`. -/
def pure158 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I16 X 8) (I8 X 16) (EXTMUL HIGH U)`. -/
def pure159 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_ishape (.X .I8 (.mk_dim 16))) (.mk_vextbinop___0 .I8 16 .I16 8 (.EXTMUL .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I32 X 4) ABS`. -/
def pure160 : Operation :=
  let instruction : instr := .VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I32 X 4) NEG`. -/
def pure161 : Operation :=
  let instruction : instr := .VUNOP (.X .I32 (.mk_dim 4)) (.mk_vunop__0 .I32 4 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VTESTOP (I32 X 4) ALL_TRUE`. -/
def pure163 : Operation :=
  let instruction : instr := .VTESTOP (.X .I32 (.mk_dim 4)) (.mk_vtestop__0 .I32 4 .ALL_TRUE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vtestop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBITMASK (I32 X 4)`. -/
def pure164 : Operation :=
  let instruction : instr := .VBITMASK (.mk_ishape (.X .I32 (.mk_dim 4)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbitmask C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (I16 X 8) (EXTEND LOW S)`. -/
def pure167 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (I16 X 8) (EXTEND HIGH S)`. -/
def pure168 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (I16 X 8) (EXTEND LOW U)`. -/
def pure169 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (I16 X 8) (EXTEND HIGH U)`. -/
def pure170 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .I16 (.mk_dim 8)) (.mk_vcvtop___0 .I16 8 .I32 4 (.EXTEND .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I32 X 4) SHL`. -/
def pure171 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 .SHL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I32 X 4) (SHR S)`. -/
def pure172 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I32 X 4) (SHR U)`. -/
def pure173 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vshiftop__0 .I32 4 (.SHR .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) ADD`. -/
def pure174 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) SUB`. -/
def pure177 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) MUL`. -/
def pure181 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 .MUL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) (MIN S)`. -/
def pure182 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) (MIN U)`. -/
def pure183 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MIN .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) (MAX S)`. -/
def pure184 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I32 X 4) (MAX U)`. -/
def pure185 : Operation :=
  let instruction : instr := .VBINOP (.X .I32 (.mk_dim 4)) (.mk_vbinop__0 .I32 4 (.MAX .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I32 X 4) (I16 X 8) (DOT S)`. -/
def pure186 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 .DOTS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I32 X 4) (I16 X 8) (EXTMUL LOW S)`. -/
def pure188 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I32 X 4) (I16 X 8) (EXTMUL HIGH S)`. -/
def pure189 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I32 X 4) (I16 X 8) (EXTMUL LOW U)`. -/
def pure190 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I32 X 4) (I16 X 8) (EXTMUL HIGH U)`. -/
def pure191 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_ishape (.X .I16 (.mk_dim 8))) (.mk_vextbinop___0 .I16 8 .I32 4 (.EXTMUL .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I64 X 2) ABS`. -/
def pure192 : Operation :=
  let instruction : instr := .VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (I64 X 2) NEG`. -/
def pure193 : Operation :=
  let instruction : instr := .VUNOP (.X .I64 (.mk_dim 2)) (.mk_vunop__0 .I64 2 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VTESTOP (I64 X 2) ALL_TRUE`. -/
def pure195 : Operation :=
  let instruction : instr := .VTESTOP (.X .I64 (.mk_dim 2)) (.mk_vtestop__0 .I64 2 .ALL_TRUE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vtestop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBITMASK (I64 X 2)`. -/
def pure196 : Operation :=
  let instruction : instr := .VBITMASK (.mk_ishape (.X .I64 (.mk_dim 2)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .test, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbitmask C _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I64 X 2) (I32 X 4) (EXTEND LOW S)`. -/
def pure199 : Operation :=
  let instruction : instr := .VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I64 X 2) (I32 X 4) (EXTEND HIGH S)`. -/
def pure200 : Operation :=
  let instruction : instr := .VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I64 X 2) (I32 X 4) (EXTEND LOW U)`. -/
def pure201 : Operation :=
  let instruction : instr := .VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I64 X 2) (I32 X 4) (EXTEND HIGH U)`. -/
def pure202 : Operation :=
  let instruction : instr := .VCVTOP (.X .I64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___0 .I32 4 .I64 2 (.EXTEND .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I64 X 2) SHL`. -/
def pure203 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 .SHL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I64 X 2) (SHR S)`. -/
def pure204 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VSHIFTOP (I64 X 2) (SHR U)`. -/
def pure205 : Operation :=
  let instruction : instr := .VSHIFTOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_vshiftop__0 .I64 2 (.SHR .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .shift, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vshiftop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I64 X 2) ADD`. -/
def pure206 : Operation :=
  let instruction : instr := .VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I64 X 2) SUB`. -/
def pure209 : Operation :=
  let instruction : instr := .VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (I64 X 2) MUL`. -/
def pure213 : Operation :=
  let instruction : instr := .VBINOP (.X .I64 (.mk_dim 2)) (.mk_vbinop__0 .I64 2 .MUL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) EQ`. -/
def pure214 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .EQ)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) NE`. -/
def pure215 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 .NE)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) (LT S)`. -/
def pure216 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) (GT S)`. -/
def pure217 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GT .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) (LE S)`. -/
def pure218 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.LE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VRELOP (I64 X 2) (GE S)`. -/
def pure219 : Operation :=
  let instruction : instr := .VRELOP (.X .I64 (.mk_dim 2)) (.mk_vrelop__0 .I64 2 (.GE .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vrelop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I64 X 2) (I32 X 4) (EXTMUL LOW S)`. -/
def pure220 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I64 X 2) (I32 X 4) (EXTMUL HIGH S)`. -/
def pure221 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I64 X 2) (I32 X 4) (EXTMUL LOW U)`. -/
def pure222 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .LOW .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VEXTBINOP (I64 X 2) (I32 X 4) (EXTMUL HIGH U)`. -/
def pure223 : Operation :=
  let instruction : instr := .VEXTBINOP (.mk_ishape (.X .I64 (.mk_dim 2))) (.mk_ishape (.X .I32 (.mk_dim 4))) (.mk_vextbinop___0 .I32 4 .I64 2 (.EXTMUL .HIGH .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vextbinop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) ABS`. -/
def pure224 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) NEG`. -/
def pure225 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F32 X 4) SQRT`. -/
def pure227 : Operation :=
  let instruction : instr := .VUNOP (.X .F32 (.mk_dim 4)) (.mk_vunop__1 .F32 4 .SQRT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) ADD`. -/
def pure228 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) SUB`. -/
def pure229 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) MUL`. -/
def pure230 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MUL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) DIV`. -/
def pure231 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .DIV)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) MIN`. -/
def pure232 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MIN)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) MAX`. -/
def pure233 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .MAX)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) PMIN`. -/
def pure234 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMIN)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F32 X 4) PMAX`. -/
def pure235 : Operation :=
  let instruction : instr := .VBINOP (.X .F32 (.mk_dim 4)) (.mk_vbinop__1 .F32 4 .PMAX)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) ABS`. -/
def pure236 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .ABS)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) NEG`. -/
def pure237 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .NEG)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VUNOP (F64 X 2) SQRT`. -/
def pure239 : Operation :=
  let instruction : instr := .VUNOP (.X .F64 (.mk_dim 2)) (.mk_vunop__1 .F64 2 .SQRT)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vunop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) ADD`. -/
def pure240 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .ADD)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) SUB`. -/
def pure241 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .SUB)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) MUL`. -/
def pure242 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MUL)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) DIV`. -/
def pure243 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .DIV)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) MIN`. -/
def pure244 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MIN)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) MAX`. -/
def pure245 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .MAX)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) PMIN`. -/
def pure246 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMIN)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VBINOP (F64 X 2) PMAX`. -/
def pure247 : Operation :=
  let instruction : instr := .VBINOP (.X .F64 (.mk_dim 2)) (.mk_vbinop__1 .F64 2 .PMAX)
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .binary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vbinop C _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (F32 X 4) (TRUNC_SAT S)`. -/
def pure248 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .S none))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (F32 X 4) (TRUNC_SAT U)`. -/
def pure249 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .F32 (.mk_dim 4)) (.mk_vcvtop___2 .F32 4 .I32 4 (.TRUNC_SAT .U none))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F32 X 4) (I32 X 4) (CONVERT S)`. -/
def pure250 : Operation :=
  let instruction : instr := .VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F32 X 4) (I32 X 4) (CONVERT U)`. -/
def pure251 : Operation :=
  let instruction : instr := .VCVTOP (.X .F32 (.mk_dim 4)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F32 4 (.CONVERT none .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (F64 X 2) (TRUNC_SAT S ZERO)`. -/
def pure252 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .S (some .ZERO)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (I32 X 4) (F64 X 2) (TRUNC_SAT U ZERO)`. -/
def pure253 : Operation :=
  let instruction : instr := .VCVTOP (.X .I32 (.mk_dim 4)) (.X .F64 (.mk_dim 2)) (.mk_vcvtop___2 .F64 2 .I32 4 (.TRUNC_SAT .U (some .ZERO)))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F64 X 2) (I32 X 4) (CONVERT LOW S)`. -/
def pure254 : Operation :=
  let instruction : instr := .VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .S))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- `VCVTOP (F64 X 2) (I32 X 4) (CONVERT LOW U)`. -/
def pure255 : Operation :=
  let instruction : instr := .VCVTOP (.X .F64 (.mk_dim 2)) (.X .I32 (.mk_dim 4)) (.mk_vcvtop___1 .I32 4 .F64 2 (.CONVERT (some .LOW) .U))
  let hwf : wf_instr instruction := by
    dsimp only [instruction]
    repeat' first | exact integer8_wf | exact integer16_wf | exact integer32_wf | exact integer64_wf | decide | constructor
  { instruction := instruction, signature := .unary, wellFormed := hwf,
    typed := fun C hC => by exact Instr_ok.vcvtop C _ _ _ hC hwf,
    declared := fun _ => by simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices],
    principal := fun _ _ _ ht => by dsimp only [instruction] at ht; cases ht; exact ⟨rfl, rfl⟩ }

/-- The SIMD instruction assigned to a `0xfd` subopcode, for instructions without immediates. -/
def pureMeaning (subopcode : Nat) : Option Operation :=
  if subopcode ≥ 256 then none else match subopcode with
  | 14 => some pure14
  | 15 => some pure15
  | 16 => some pure16
  | 17 => some pure17
  | 18 => some pure18
  | 19 => some pure19
  | 20 => some pure20
  | 35 => some pure35
  | 36 => some pure36
  | 37 => some pure37
  | 38 => some pure38
  | 39 => some pure39
  | 40 => some pure40
  | 41 => some pure41
  | 42 => some pure42
  | 43 => some pure43
  | 44 => some pure44
  | 45 => some pure45
  | 46 => some pure46
  | 47 => some pure47
  | 48 => some pure48
  | 49 => some pure49
  | 50 => some pure50
  | 51 => some pure51
  | 52 => some pure52
  | 53 => some pure53
  | 54 => some pure54
  | 55 => some pure55
  | 56 => some pure56
  | 57 => some pure57
  | 58 => some pure58
  | 59 => some pure59
  | 60 => some pure60
  | 61 => some pure61
  | 62 => some pure62
  | 63 => some pure63
  | 64 => some pure64
  | 65 => some pure65
  | 66 => some pure66
  | 67 => some pure67
  | 68 => some pure68
  | 69 => some pure69
  | 70 => some pure70
  | 71 => some pure71
  | 72 => some pure72
  | 73 => some pure73
  | 74 => some pure74
  | 75 => some pure75
  | 76 => some pure76
  | 77 => some pure77
  | 78 => some pure78
  | 79 => some pure79
  | 80 => some pure80
  | 81 => some pure81
  | 82 => some pure82
  | 83 => some pure83
  | 94 => some pure94
  | 95 => some pure95
  | 96 => some pure96
  | 97 => some pure97
  | 98 => some pure98
  | 99 => some pure99
  | 100 => some pure100
  | 101 => some pure101
  | 102 => some pure102
  | 103 => some pure103
  | 104 => some pure104
  | 105 => some pure105
  | 106 => some pure106
  | 107 => some pure107
  | 108 => some pure108
  | 109 => some pure109
  | 110 => some pure110
  | 111 => some pure111
  | 112 => some pure112
  | 113 => some pure113
  | 114 => some pure114
  | 115 => some pure115
  | 116 => some pure116
  | 117 => some pure117
  | 118 => some pure118
  | 119 => some pure119
  | 120 => some pure120
  | 121 => some pure121
  | 122 => some pure122
  | 123 => some pure123
  | 124 => some pure124
  | 125 => some pure125
  | 126 => some pure126
  | 127 => some pure127
  | 128 => some pure128
  | 129 => some pure129
  | 130 => some pure130
  | 131 => some pure131
  | 132 => some pure132
  | 133 => some pure133
  | 134 => some pure134
  | 135 => some pure135
  | 136 => some pure136
  | 137 => some pure137
  | 138 => some pure138
  | 139 => some pure139
  | 140 => some pure140
  | 141 => some pure141
  | 142 => some pure142
  | 143 => some pure143
  | 144 => some pure144
  | 145 => some pure145
  | 146 => some pure146
  | 147 => some pure147
  | 148 => some pure148
  | 149 => some pure149
  | 150 => some pure150
  | 151 => some pure151
  | 152 => some pure152
  | 153 => some pure153
  | 155 => some pure155
  | 156 => some pure156
  | 157 => some pure157
  | 158 => some pure158
  | 159 => some pure159
  | 160 => some pure160
  | 161 => some pure161
  | 163 => some pure163
  | 164 => some pure164
  | 167 => some pure167
  | 168 => some pure168
  | 169 => some pure169
  | 170 => some pure170
  | 171 => some pure171
  | 172 => some pure172
  | 173 => some pure173
  | 174 => some pure174
  | 177 => some pure177
  | 181 => some pure181
  | 182 => some pure182
  | 183 => some pure183
  | 184 => some pure184
  | 185 => some pure185
  | 186 => some pure186
  | 188 => some pure188
  | 189 => some pure189
  | 190 => some pure190
  | 191 => some pure191
  | 192 => some pure192
  | 193 => some pure193
  | 195 => some pure195
  | 196 => some pure196
  | 199 => some pure199
  | 200 => some pure200
  | 201 => some pure201
  | 202 => some pure202
  | 203 => some pure203
  | 204 => some pure204
  | 205 => some pure205
  | 206 => some pure206
  | 209 => some pure209
  | 213 => some pure213
  | 214 => some pure214
  | 215 => some pure215
  | 216 => some pure216
  | 217 => some pure217
  | 218 => some pure218
  | 219 => some pure219
  | 220 => some pure220
  | 221 => some pure221
  | 222 => some pure222
  | 223 => some pure223
  | 224 => some pure224
  | 225 => some pure225
  | 227 => some pure227
  | 228 => some pure228
  | 229 => some pure229
  | 230 => some pure230
  | 231 => some pure231
  | 232 => some pure232
  | 233 => some pure233
  | 234 => some pure234
  | 235 => some pure235
  | 236 => some pure236
  | 237 => some pure237
  | 239 => some pure239
  | 240 => some pure240
  | 241 => some pure241
  | 242 => some pure242
  | 243 => some pure243
  | 244 => some pure244
  | 245 => some pure245
  | 246 => some pure246
  | 247 => some pure247
  | 248 => some pure248
  | 249 => some pure249
  | 250 => some pure250
  | 251 => some pure251
  | 252 => some pure252
  | 253 => some pure253
  | 254 => some pure254
  | 255 => some pure255
  | _ => none

/-- Pure SIMD subopcodes are below 256. -/
theorem pure_bound {opcode op} (hmap : pureMeaning opcode = some op) : opcode < 256 := by
  unfold pureMeaning at hmap
  split at hmap
  · contradiction
  · omega

end Itasca.Wasm2.Simd
