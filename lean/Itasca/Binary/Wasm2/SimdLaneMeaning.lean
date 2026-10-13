import Itasca.Binary.Wasm2.SimdPureMeaning
import Mathlib.Tactic.CasesM

/-!
# Wasm 2.0 SIMD lane instructions

`Simd.LaneOperation` lists the fourteen SIMD extract and replace lane instructions, with their
shape, lane count and stack types. `LaneOperation.typed` shows that `Instr_ok` types each when
the lane index is in range, `LaneOperation.principal` and `LaneOperation.bound` recover the stack
effect and the lane bound from a generated typing, and `laneMeaning` maps subopcodes 21 to 34 to
operations.
-/

namespace Itasca.Wasm2.Simd

/-- The fourteen lane instructions, with the signedness forms Wasm 2.0 admits. -/
inductive LaneOperation where
  | i8x16ExtractS
  | i8x16ExtractU
  | i8x16Replace
  | i16x8ExtractS
  | i16x8ExtractU
  | i16x8Replace
  | i32x4Extract
  | i32x4Replace
  | i64x2Extract
  | i64x2Replace
  | f32x4Extract
  | f32x4Replace
  | f64x2Extract
  | f64x2Replace
  deriving DecidableEq

/-- The vector shape of a lane instruction. -/
def LaneOperation.shape : LaneOperation → shape
  | .i8x16ExtractS => .X .I8 (.mk_dim 16)
  | .i8x16ExtractU => .X .I8 (.mk_dim 16)
  | .i8x16Replace => .X .I8 (.mk_dim 16)
  | .i16x8ExtractS => .X .I16 (.mk_dim 8)
  | .i16x8ExtractU => .X .I16 (.mk_dim 8)
  | .i16x8Replace => .X .I16 (.mk_dim 8)
  | .i32x4Extract => .X .I32 (.mk_dim 4)
  | .i32x4Replace => .X .I32 (.mk_dim 4)
  | .i64x2Extract => .X .I64 (.mk_dim 2)
  | .i64x2Replace => .X .I64 (.mk_dim 2)
  | .f32x4Extract => .X .F32 (.mk_dim 4)
  | .f32x4Replace => .X .F32 (.mk_dim 4)
  | .f64x2Extract => .X .F64 (.mk_dim 2)
  | .f64x2Replace => .X .F64 (.mk_dim 2)

/-- The number of lanes of a lane instruction's shape. -/
def LaneOperation.count : LaneOperation → Nat
  | .i8x16ExtractS => 16
  | .i8x16ExtractU => 16
  | .i8x16Replace => 16
  | .i16x8ExtractS => 8
  | .i16x8ExtractU => 8
  | .i16x8Replace => 8
  | .i32x4Extract => 4
  | .i32x4Replace => 4
  | .i64x2Extract => 2
  | .i64x2Replace => 2
  | .f32x4Extract => 4
  | .f32x4Replace => 4
  | .f64x2Extract => 2
  | .f64x2Replace => 2

/-- The scalar type moved in or out of a lane. -/
def LaneOperation.scalar : LaneOperation → numtype
  | .i8x16ExtractS => .I32
  | .i8x16ExtractU => .I32
  | .i8x16Replace => .I32
  | .i16x8ExtractS => .I32
  | .i16x8ExtractU => .I32
  | .i16x8Replace => .I32
  | .i32x4Extract => .I32
  | .i32x4Replace => .I32
  | .i64x2Extract => .I64
  | .i64x2Replace => .I64
  | .f32x4Extract => .F32
  | .f32x4Replace => .F32
  | .f64x2Extract => .F64
  | .f64x2Replace => .F64

/-- Whether the operation replaces a lane, as opposed to extracting one. -/
def LaneOperation.replace : LaneOperation → Bool
  | .i8x16ExtractS => false
  | .i8x16ExtractU => false
  | .i8x16Replace => true
  | .i16x8ExtractS => false
  | .i16x8ExtractU => false
  | .i16x8Replace => true
  | .i32x4Extract => false
  | .i32x4Replace => true
  | .i64x2Extract => false
  | .i64x2Replace => true
  | .f32x4Extract => false
  | .f32x4Replace => true
  | .f64x2Extract => false
  | .f64x2Replace => true

/-- The signedness of a packed extract, if any. -/
def LaneOperation.extension : LaneOperation → Option sx
  | .i8x16ExtractS => some .S
  | .i8x16ExtractU => some .U
  | .i8x16Replace => none
  | .i16x8ExtractS => some .S
  | .i16x8ExtractU => some .U
  | .i16x8Replace => none
  | .i32x4Extract => none
  | .i32x4Replace => none
  | .i64x2Extract => none
  | .i64x2Replace => none
  | .f32x4Extract => none
  | .f32x4Replace => none
  | .f64x2Extract => none
  | .f64x2Replace => none

/-- The SpecTec instruction of a lane operation at a lane index. -/
def LaneOperation.instruction (op : LaneOperation) (lane : laneidx) : instr :=
  if op.replace then .VREPLACE_LANE op.shape lane else .VEXTRACT_LANE op.shape op.extension lane

/-- The operand types of a lane operation. -/
def LaneOperation.inputs (op : LaneOperation) : List valtype :=
  if op.replace then [.V128, valtype_numtype op.scalar] else [.V128]

/-- The result types of a lane operation. -/
def LaneOperation.outputs (op : LaneOperation) : List valtype :=
  if op.replace then [.V128] else [valtype_numtype op.scalar]

/-- A lane operation with a byte lane index is well formed. -/
theorem LaneOperation.wellFormed (op : LaneOperation) (lane : laneidx) (h : wf_uN 8 lane) :
    wf_instr (op.instruction lane) := by
  cases op <;> simp only [instruction, shape, replace, extension, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first | exact h | decide | constructor

/-- A lane operation with an in-range lane index has its stack effect under `Instr_ok`. -/
theorem LaneOperation.typed (op : LaneOperation) (C : context) (lane : laneidx)
    (hC : wf_context C) (h8 : wf_uN 8 lane) (hl : proj_uN_0 lane < op.count) :
    Instr_ok C (op.instruction lane)
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hw := op.wellFormed lane h8
  cases op
  case i8x16ExtractS =>
    exact Instr_ok.vextract_lane C (.X .I8 (.mk_dim 16)) (some .S) lane (.mk_dim 16)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i8x16ExtractU =>
    exact Instr_ok.vextract_lane C (.X .I8 (.mk_dim 16)) (some .U) lane (.mk_dim 16)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i8x16Replace =>
    exact Instr_ok.vreplace_lane C (.X .I8 (.mk_dim 16)) lane (.mk_dim 16)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i16x8ExtractS =>
    exact Instr_ok.vextract_lane C (.X .I16 (.mk_dim 8)) (some .S) lane (.mk_dim 8)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i16x8ExtractU =>
    exact Instr_ok.vextract_lane C (.X .I16 (.mk_dim 8)) (some .U) lane (.mk_dim 8)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i16x8Replace =>
    exact Instr_ok.vreplace_lane C (.X .I16 (.mk_dim 8)) lane (.mk_dim 8)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i32x4Extract =>
    exact Instr_ok.vextract_lane C (.X .I32 (.mk_dim 4)) none lane (.mk_dim 4)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i32x4Replace =>
    exact Instr_ok.vreplace_lane C (.X .I32 (.mk_dim 4)) lane (.mk_dim 4)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i64x2Extract =>
    exact Instr_ok.vextract_lane C (.X .I64 (.mk_dim 2)) none lane (.mk_dim 2)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case i64x2Replace =>
    exact Instr_ok.vreplace_lane C (.X .I64 (.mk_dim 2)) lane (.mk_dim 2)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case f32x4Extract =>
    exact Instr_ok.vextract_lane C (.X .F32 (.mk_dim 4)) none lane (.mk_dim 4)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case f32x4Replace =>
    exact Instr_ok.vreplace_lane C (.X .F32 (.mk_dim 4)) lane (.mk_dim 4)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case f64x2Extract =>
    exact Instr_ok.vextract_lane C (.X .F64 (.mk_dim 2)) none lane (.mk_dim 2)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw
  case f64x2Replace =>
    exact Instr_ok.vreplace_lane C (.X .F64 (.mk_dim 2)) lane (.mk_dim 2)
      (by repeat' first | decide | constructor) hl hC (by constructor; decide) hw

/-- A generated typing of a lane operation has the operation's stack effect. -/
theorem LaneOperation.principal (op : LaneOperation) (C : context) (lane : laneidx)
    (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs ∧ outs = op.outputs := by
  cases op <;> simp only [instruction, shape, replace, extension,
    Bool.false_eq_true, ↓reduceIte] at ht <;> cases ht <;> exact ⟨rfl, rfl⟩

/-- A generated typing of a lane operation bounds the lane index by the lane count. -/
theorem LaneOperation.bound (op : LaneOperation) (C : context) (lane : laneidx)
    (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    proj_uN_0 lane < op.count := by
  cases op <;> simp only [instruction, shape, replace, extension,
    Bool.false_eq_true, ↓reduceIte] at ht <;> cases ht
  all_goals cases_type fun_dim
  all_goals assumption


/-- A lane operation has no declared-reference obligation. -/
theorem LaneOperation.declared (op : LaneOperation) (refs : List funcidx) (lane : laneidx) :
    DeclaredReferences.Instruction refs (op.instruction lane) := by
  cases op <;> simp [instruction, replace, DeclaredReferences.Instruction,
    DeclaredReferences.instructionIndices]

/-- The lane operation assigned to a `0xfd` subopcode (21 to 34). -/
def laneMeaning (opcode : Nat) : Option LaneOperation :=
  match opcode with
  | 21 => some .i8x16ExtractS
  | 22 => some .i8x16ExtractU
  | 23 => some .i8x16Replace
  | 24 => some .i16x8ExtractS
  | 25 => some .i16x8ExtractU
  | 26 => some .i16x8Replace
  | 27 => some .i32x4Extract
  | 28 => some .i32x4Replace
  | 29 => some .i64x2Extract
  | 30 => some .i64x2Replace
  | 31 => some .f32x4Extract
  | 32 => some .f32x4Replace
  | 33 => some .f64x2Extract
  | 34 => some .f64x2Replace
  | _ => none

end Itasca.Wasm2.Simd
