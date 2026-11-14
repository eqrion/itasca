import Itasca.Support.Result
import Itasca.Binary.Wasm1.EncodingComplete
import Itasca.Spec.Checks
import Itasca.Binary.Wasm2.BlockType
import Itasca.Binary.Wasm2.SimdPureMeaning
import Mathlib.Tactic.CasesM
import Itasca.Binary.Wasm2.Syntax

/-!
Sections, each formerly its own module: Bulk, NumericExtensions, References, SimdLaneMeaning, SimdMemoryMeaning, DeclaredReferences.
-/

/-! ## Bulk -/

section

/-!
# Wasm 2.0 bulk memory and table bytes

`BulkBinary.Immediate` relates the `0xfc` subopcodes 8 to 17 (`memory.init` through
`table.fill`) to their SpecTec instructions and immediate bytes. `Immediate.wellFormed` shows
that each satisfies `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.BulkBinary

/-- The immediates of bulk memory and table instructions after their `0xfc` subopcode. Memory
indices are reserved literal zero bytes. -/
inductive Immediate : U32 → instr → List U8 → Prop where
  | memoryInit (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 8#u32 (.MEMORY_INIT (.mk_uN index.val)) (bytes ++ [0#u8])
  | dataDrop (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 9#u32 (.DATA_DROP (.mk_uN index.val)) bytes
  | memoryCopy : Immediate 10#u32 .MEMORY_COPY [0#u8, 0#u8]
  | memoryFill : Immediate 11#u32 .MEMORY_FILL [0#u8]
  | tableInit (element table : U32) {elementBytes tableBytes} :
      Leb128.Encoding elementBytes element.val → Leb128.Encoding tableBytes table.val →
      Immediate 12#u32 (.TABLE_INIT (.mk_uN table.val) (.mk_uN element.val))
        (elementBytes ++ tableBytes)
  | elemDrop (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 13#u32 (.ELEM_DROP (.mk_uN index.val)) bytes
  | tableCopy (destination source : U32) {destinationBytes sourceBytes} :
      Leb128.Encoding destinationBytes destination.val → Leb128.Encoding sourceBytes source.val →
      Immediate 14#u32 (.TABLE_COPY (.mk_uN destination.val) (.mk_uN source.val))
        (destinationBytes ++ sourceBytes)
  | tableGrow (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 15#u32 (.TABLE_GROW (.mk_uN index.val)) bytes
  | tableSize (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 16#u32 (.TABLE_SIZE (.mk_uN index.val)) bytes
  | tableFill (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 17#u32 (.TABLE_FILL (.mk_uN index.val)) bytes

/-- Bulk subopcodes lie between 8 and 17. -/
theorem Immediate.subopcode_range {subopcode op bytes} (h : Immediate subopcode op bytes) :
    8 ≤ subopcode.val ∧ subopcode.val ≤ 17 := by
  cases h <;> decide

end Itasca.Wasm2.BulkBinary

end

/-! ## NumericExtensions -/

section

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

end

/-! ## References -/

section

/-!
# Wasm 2.0 reference instruction bytes

`ReferencesBinary.Immediate` relates the opcodes of `ref.null`, `ref.is_null`, `ref.func`,
typed `select`, `table.get`, `table.set` and the Wasm 2.0 `call_indirect` to their SpecTec
instructions and immediate bytes. `Immediate.wellFormed` shows that each satisfies `wf_instr`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.ReferencesBinary

/-- The reference type tag is the literal byte `0x70` or `0x6f`. -/
def referenceByte : wasm_types.ElemType → U8
  | .FuncRef => 0x70#u8
  | .ExternRef => 0x6f#u8

/-- The immediates of reference, typed select, table access and indirect call instructions. Index
encodings admit every valid unsigned LEB128. -/
inductive Immediate : U8 → instr → List U8 → Prop where
  | refNull (rt : wasm_types.ElemType) :
      Immediate 0xd0#u8 (.REF_NULL (Translate.referenceType rt)) [referenceByte rt]
  | refIsNull : Immediate 0xd1#u8 .REF_IS_NULL []
  | refFunc (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0xd2#u8 (.REF_FUNC (.mk_uN index.val)) bytes
  | selectTyped (ty : wasm_types.ValueType) {count} : Leb128.Encoding count 1 →
      Immediate 0x1c#u8 (.SELECT (some [Translate.valueType ty])) (count ++ [valueByte ty])
  | tableGet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x25#u8 (.TABLE_GET (.mk_uN index.val)) bytes
  | tableSet (index : U32) {bytes} : Leb128.Encoding bytes index.val →
      Immediate 0x26#u8 (.TABLE_SET (.mk_uN index.val)) bytes
  | callIndirect (typeIndex tableIndex : U32) {typeBytes tableBytes} :
      Leb128.Encoding typeBytes typeIndex.val → Leb128.Encoding tableBytes tableIndex.val →
      Immediate 0x11#u8 (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        (typeBytes ++ tableBytes)

end Itasca.Wasm2.ReferencesBinary

end

/-! ## SimdLaneMeaning -/

section

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

end

/-! ## SimdMemoryMeaning -/

section

/-!
# Wasm 2.0 SIMD memory instructions

`Simd.MemoryOperation` lists the vector loads, stores, splat loads, zero-extending loads and lane
loads and stores, with their natural alignment, lane count and stack types.
`MemoryOperation.typed` shows that `Instr_ok` types each when the memory exists and the alignment
and lane are in bounds, `MemoryOperation.principal` recovers the stack effect, and `memoryMeaning`
maps subopcodes 0 to 11 and 84 to 93 to operations. `lane_pure_none`, `memory_pure_none` and
`memory_lane_none` show that the SIMD opcode tables do not overlap.
-/

namespace Itasca.Wasm2.Simd

/-- The vector memory instructions of Wasm 2.0. -/
inductive MemoryOperation where
  | load
  | load8x8S
  | load8x8U
  | load16x4S
  | load16x4U
  | load32x2S
  | load32x2U
  | splat8
  | splat16
  | splat32
  | splat64
  | storeFull
  | load8Lane
  | load16Lane
  | load32Lane
  | load64Lane
  | store8Lane
  | store16Lane
  | store32Lane
  | store64Lane
  | load32Zero
  | load64Zero

/-- The natural alignment exponent of a memory operation. -/
def MemoryOperation.naturalAlign : MemoryOperation → Nat
  | .load => 4
  | .load8x8S => 3
  | .load8x8U => 3
  | .load16x4S => 3
  | .load16x4U => 3
  | .load32x2S => 3
  | .load32x2U => 3
  | .splat8 => 0
  | .splat16 => 1
  | .splat32 => 2
  | .splat64 => 3
  | .storeFull => 4
  | .load8Lane => 0
  | .load16Lane => 1
  | .load32Lane => 2
  | .load64Lane => 3
  | .store8Lane => 0
  | .store16Lane => 1
  | .store32Lane => 2
  | .store64Lane => 3
  | .load32Zero => 2
  | .load64Zero => 3

/-- The lane count of a lane load or store, and 0 for the other operations. -/
def MemoryOperation.laneCount : MemoryOperation → Nat
  | .load => 0
  | .load8x8S => 0
  | .load8x8U => 0
  | .load16x4S => 0
  | .load16x4U => 0
  | .load32x2S => 0
  | .load32x2U => 0
  | .splat8 => 0
  | .splat16 => 0
  | .splat32 => 0
  | .splat64 => 0
  | .storeFull => 0
  | .load8Lane => 16
  | .load16Lane => 8
  | .load32Lane => 4
  | .load64Lane => 2
  | .store8Lane => 16
  | .store16Lane => 8
  | .store32Lane => 4
  | .store64Lane => 2
  | .load32Zero => 0
  | .load64Zero => 0

/-- Whether the operation writes memory. -/
def MemoryOperation.store : MemoryOperation → Bool
  | .load => false
  | .load8x8S => false
  | .load8x8U => false
  | .load16x4S => false
  | .load16x4U => false
  | .load32x2S => false
  | .load32x2U => false
  | .splat8 => false
  | .splat16 => false
  | .splat32 => false
  | .splat64 => false
  | .storeFull => true
  | .load8Lane => false
  | .load16Lane => false
  | .load32Lane => false
  | .load64Lane => false
  | .store8Lane => true
  | .store16Lane => true
  | .store32Lane => true
  | .store64Lane => true
  | .load32Zero => false
  | .load64Zero => false

/-- The SpecTec instruction of a memory operation at a memory argument and lane index. The lane
index is ignored by operations without lanes. -/
def MemoryOperation.instruction (op : MemoryOperation) (arg : memarg) (lane : laneidx) : instr :=
  match op with
  | .load => .VLOAD .V128 none arg
  | .load8x8S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .S)) arg
  | .load8x8U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 8) 8 .U)) arg
  | .load16x4S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .S)) arg
  | .load16x4U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 16) 4 .U)) arg
  | .load32x2S => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .S)) arg
  | .load32x2U => .VLOAD .V128 (some (.SHAPEX_ (.mk_sz 32) 2 .U)) arg
  | .splat8 => .VLOAD .V128 (some (.SPLAT (.mk_sz 8))) arg
  | .splat16 => .VLOAD .V128 (some (.SPLAT (.mk_sz 16))) arg
  | .splat32 => .VLOAD .V128 (some (.SPLAT (.mk_sz 32))) arg
  | .splat64 => .VLOAD .V128 (some (.SPLAT (.mk_sz 64))) arg
  | .storeFull => .VSTORE .V128 arg
  | .load8Lane => .VLOAD_LANE .V128 (.mk_sz 8) arg lane
  | .load16Lane => .VLOAD_LANE .V128 (.mk_sz 16) arg lane
  | .load32Lane => .VLOAD_LANE .V128 (.mk_sz 32) arg lane
  | .load64Lane => .VLOAD_LANE .V128 (.mk_sz 64) arg lane
  | .store8Lane => .VSTORE_LANE .V128 (.mk_sz 8) arg lane
  | .store16Lane => .VSTORE_LANE .V128 (.mk_sz 16) arg lane
  | .store32Lane => .VSTORE_LANE .V128 (.mk_sz 32) arg lane
  | .store64Lane => .VSTORE_LANE .V128 (.mk_sz 64) arg lane
  | .load32Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 32))) arg
  | .load64Zero => .VLOAD .V128 (some (.ZERO (.mk_sz 64))) arg

/-- The operand types of a memory operation. -/
def MemoryOperation.inputs (op : MemoryOperation) : List valtype :=
  if op.store || op.laneCount != 0 then [.I32, .V128] else [.I32]

/-- The result types of a memory operation. -/
def MemoryOperation.outputs (op : MemoryOperation) : List valtype :=
  if op.store then [] else [.V128]

/-- A memory operation with a well-formed memory argument and byte lane index is well formed. -/
theorem MemoryOperation.wellFormed (op : MemoryOperation) (arg : memarg) (lane : laneidx)
    (ha : wf_memarg arg) (hl : wf_uN 8 lane) : wf_instr (op.instruction arg lane) := by
  cases op <;> simp only [instruction]
  all_goals constructor
  all_goals try exact ha
  all_goals try exact hl
  all_goals try (simp only [Forall, Option.toList_none, List.not_mem_nil, false_implies, implies_true])
  all_goals try (simp only [Option.toList_some, List.mem_singleton]; intro value he; subst value)
  all_goals repeat' first | exact ha | exact hl | decide | constructor
  all_goals norm_num [proj_sz_0, vsize]

/-- A memory operation has its stack effect under `Instr_ok`, given memory zero, an alignment within
the natural alignment and an in-range lane for lane operations. -/
theorem MemoryOperation.typed (op : MemoryOperation) (C : context) (arg : memarg) (lane : laneidx)
    (mt : memtype) (hm : 0 < C.MEMS.length) (he : C.MEMS[0]! = mt)
    (hC : wf_context C) (hmt : wf_memtype mt) (ha : wf_memarg arg) (h8 : wf_uN 8 lane)
    (halign : (2 : Rat) ^ proj_uN_0 arg.ALIGN ≤ (2 : Rat) ^ op.naturalAlign)
    (hlane : op.laneCount ≠ 0 → proj_uN_0 lane < op.laneCount) :
    Instr_ok C (op.instruction arg lane)
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hw := op.wellFormed arg lane ha h8
  cases op
  case load =>
    exact Instr_ok.vload_val C  arg mt hm he (by decide) (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8x8S =>
    exact Instr_ok.vload_pack C 8 8 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8x8U =>
    exact Instr_ok.vload_pack C 8 8 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load16x4S =>
    exact Instr_ok.vload_pack C 16 4 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load16x4U =>
    exact Instr_ok.vload_pack C 16 4 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load32x2S =>
    exact Instr_ok.vload_pack C 32 2 .S arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load32x2U =>
    exact Instr_ok.vload_pack C 32 2 .U arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat8 =>
    exact Instr_ok.vload_splat C 8 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat16 =>
    exact Instr_ok.vload_splat C 16 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat32 =>
    exact Instr_ok.vload_splat C 32 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case splat64 =>
    exact Instr_ok.vload_splat C 64 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case storeFull =>
    exact Instr_ok.vstore C  arg mt hm he (by decide) (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load8Lane =>
    exact Instr_ok.vload_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load16Lane =>
    exact Instr_ok.vload_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Lane =>
    exact Instr_ok.vload_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load64Lane =>
    exact Instr_ok.vload_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store8Lane =>
    exact Instr_ok.vstore_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store16Lane =>
    exact Instr_ok.vstore_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store32Lane =>
    exact Instr_ok.vstore_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store64Lane =>
    exact Instr_ok.vstore_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Zero =>
    exact Instr_ok.vload_zero C 32 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw
  case load64Zero =>
    exact Instr_ok.vload_zero C 64 arg mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) hC hmt hw

/-- A generated typing of a memory operation has the operation's stack effect. -/
theorem MemoryOperation.principal (op : MemoryOperation) (C : context) (arg : memarg)
    (lane : laneidx) (ins outs : List valtype)
    (ht : Instr_ok C (op.instruction arg lane) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs ∧ outs = op.outputs := by
  cases op <;> simp only [instruction] at ht <;> cases ht <;> exact ⟨rfl, rfl⟩

/-- A memory operation has no declared-reference obligation. -/
theorem MemoryOperation.declared (op : MemoryOperation) (refs : List funcidx) (arg : memarg) (lane : laneidx) :
    DeclaredReferences.Instruction refs (op.instruction arg lane) := by
  cases op <;> simp [instruction, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]

/-- The memory operation assigned to a `0xfd` subopcode. `load64_zero` is opcode 93 as in the
published specification. The pinned SpecTec binary table lists 92 twice. -/
def memoryMeaning (opcode : Nat) : Option MemoryOperation :=
  match opcode with
  | 0 => some .load
  | 1 => some .load8x8S
  | 2 => some .load8x8U
  | 3 => some .load16x4S
  | 4 => some .load16x4U
  | 5 => some .load32x2S
  | 6 => some .load32x2U
  | 7 => some .splat8
  | 8 => some .splat16
  | 9 => some .splat32
  | 10 => some .splat64
  | 11 => some .storeFull
  | 84 => some .load8Lane
  | 85 => some .load16Lane
  | 86 => some .load32Lane
  | 87 => some .load64Lane
  | 88 => some .store8Lane
  | 89 => some .store16Lane
  | 90 => some .store32Lane
  | 91 => some .store64Lane
  | 92 => some .load32Zero
  | 93 => some .load64Zero
  | _ => none

/-- A subopcode with a lane meaning has no pure meaning. -/
theorem lane_pure_none {opcode : Nat} {op : LaneOperation}
    (h : laneMeaning opcode = some op) : pureMeaning opcode = none := by
  unfold laneMeaning at h
  split at h <;> first | rfl | contradiction

/-- A subopcode with a memory meaning has no pure meaning. -/
theorem memory_pure_none {opcode : Nat} {op : MemoryOperation}
    (h : memoryMeaning opcode = some op) : pureMeaning opcode = none := by
  unfold memoryMeaning at h
  split at h <;> first | rfl | contradiction

/-- A subopcode with a memory meaning has no lane meaning. -/
theorem memory_lane_none {opcode : Nat} {op : MemoryOperation}
    (h : memoryMeaning opcode = some op) : laneMeaning opcode = none := by
  unfold memoryMeaning at h
  split at h <;> first | rfl | contradiction

end Itasca.Wasm2.Simd

end

/-! ## DeclaredReferences -/

section

/-!
# Declared references in Wasm 2.0 syntax

Transfers the `C.refs` condition of `Spec/DeclaredReferences` to flat tokens: `Emits.declared_iff`
and `BodyTokens.declared_iff` show that `TokensDeclared` holds exactly when the spelled
instructions meet `DeclaredReferences.Instructions`.
-/

namespace Itasca.Wasm2

/-- Only plain instruction tokens carry declared-reference obligations. -/
def Token.Declared (refs : List funcidx) : Token → Prop
  | .plain op => DeclaredReferences.Instruction refs op
  | _ => True

/-- Every token of the list meets its declared-reference obligation. -/
def TokensDeclared (refs : List funcidx) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.Declared refs

@[simp] theorem tokensDeclared_nil (refs : List funcidx) : TokensDeclared refs [] := by
  simp [TokensDeclared]

@[simp] theorem tokensDeclared_append (refs : List funcidx) (a b : List Token) :
    TokensDeclared refs (a ++ b) ↔ TokensDeclared refs a ∧ TokensDeclared refs b := by
  simp [TokensDeclared, or_imp, forall_and]

@[simp] theorem tokensDeclared_singleton (refs : List funcidx) (token : Token) :
    TokensDeclared refs [token] ↔ token.Declared refs := by
  simp [TokensDeclared]

@[simp] theorem tokensDeclared_cons (refs : List funcidx) (token : Token) (tokens : List Token) :
    TokensDeclared refs (token :: tokens) ↔ token.Declared refs ∧ TokensDeclared refs tokens := by
  simp [TokensDeclared, or_imp, forall_and]

/-- Tokens meet their obligations exactly when the instructions they spell do. -/
theorem Emits.declared_iff {tokens ops} (h : Emits tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ DeclaredReferences.Instructions refs ops := by
  induction h with
  | nil => simp
  | simple _ hs ih =>
    cases hs
    simp [Token.Declared, ih]
  | block bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | loop bt _ _ ih hb => simp [Token.Declared, ih, hb]
  | ifElse bt _ _ _ ih ht he => simp [Token.Declared, ih, ht, he]
  | ifEnd bt _ _ ih hb => simp [Token.Declared, ih, hb]

/-- A body's tokens meet their obligations exactly when its instructions do. -/
theorem BodyTokens.declared_iff {tokens ops} (h : BodyTokens tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ DeclaredReferences.Instructions refs ops := by
  obtain ⟨inner, rfl, he⟩ := h
  simpa [Token.Declared] using he.declared_iff refs

end Itasca.Wasm2

end
