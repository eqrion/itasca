import WebAssembly.Binary.InstructionUnique
import WebAssembly.Binary.SyntaxUnique
import Itasca.Binary.InstructionSource
import Itasca.Binary.Definitions
import Itasca.Binary.Scalar.NumericOperations
import Itasca.Binary.Body.SimdPureMeaning
import Aeneas
import WebAssembly
import Itasca.Spec.Typing
import Itasca.Results.Definitions.Binary
import Itasca.Support.Translation
import Itasca.Binary.Scalar.Encoding
import Itasca.Binary.Body.Syntax
import Mathlib.Tactic.CasesM
import Itasca.Binary.LebReaders
import Itasca.Binary.ModuleUnique

open WebAssembly

/-!
Proofs for Binary / Body.

This module collects OpcodeMeaning, Encoding.
Each section documents its contracts and consumers.
-/

/-! ## OpcodeMeaning -/

section

/-!
# Instruction-family grammar properties

Independent bulk, numeric, reference and SIMD meanings establish well-formedness and declared-reference facts for the complete instruction grammar.
-/

/-! ## SimdPureMeaning -/

section SimdPureMeaning

/-!
# Wasm 2.0 SIMD instructions without immediates

`Simd.pureMeaning` maps literal subopcodes to independently specified operation
rows. Each row carries its generated instruction, stack signature,
well-formedness, typing, declared-reference and principal-typing evidence.
`pure_bound` gives the table's opcode range. The public table is independent
of the extracted dispatcher.
-/

namespace Itasca.Body.Simd

/-- Pure SIMD subopcodes are below 256. -/
theorem pure_bound {opcode op} (hmap : pureMeaning opcode = some op) : opcode < 256 := by
  unfold pureMeaning at hmap
  split at hmap
  · contradiction
  · omega

end Itasca.Body.Simd

end SimdPureMeaning

/-! ## DeclaredReferences -/

section DeclaredReferences

/-! ## Bulk -/

section

/-!
# Wasm 2.0 bulk memory and table bytes

`BulkBinary.Immediate` relates the `0xfc` subopcodes 8 to 17 (`memory.init` through
`table.fill`) to their SpecTec instructions and immediate bytes. The operation-specific
range and declaration lemmas retain their independent source meaning.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.BulkBinary

/-- Bulk subopcodes lie between 8 and 17. -/
theorem Immediate.subopcode_range {subopcode op bytes} (h : Immediate subopcode op bytes) :
    8 ≤ subopcode.val ∧ subopcode.val ≤ 17 := by
  cases h <;> decide

end Itasca.Body.BulkBinary

end

/-! ## NumericExtensions -/

section

/-!
# Wasm 2.0 numeric additions

The sign-extension opcodes `0xc0` to `0xc4` and the saturating truncation subopcodes 0 to 7 under
`0xfc`, as `Body.Numeric.Operation` rows (`signMeaning`, `saturatingMeaning`). Each row carries a
proof that it is well formed and typed by `Instr_ok`. `sign_signature` and `saturating_signature`
recover the stack effect from a generated typing, and `sign_declared` and `saturating_declared`
show that the rows carry no `ref.func`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.NumericExtensions

/-- A generated typing of a sign-extension row has the row's stack effect. -/
theorem sign_signature {opcode op} (hmap : signMeaning opcode = some op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translation.valueType ∧ outs = [Translation.valueType op.output] := by
  unfold signMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; cases ht; exact ⟨rfl, rfl⟩

/-- A generated typing of a saturating truncation row has the row's stack effect. -/
theorem saturating_signature {opcode op} (hmap : saturatingMeaning opcode = some op)
    (C : context) (ins outs : List valtype)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = op.inputs.map Translation.valueType ∧ outs = [Translation.valueType op.output] := by
  unfold saturatingMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; cases ht; exact ⟨rfl, rfl⟩

/-- Sign-extension rows have no declared-reference obligation. -/
theorem sign_declared {opcode op} (hmap : signMeaning opcode = some op) (refs : List funcidx) :
    Spec.DeclaredReferences.Instruction refs op.instruction := by
  unfold signMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; simp [i32Extend8, i32Extend16, i64Extend8, i64Extend16, i64Extend32,
    Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

/-- Saturating truncation rows have no declared-reference obligation. -/
theorem saturating_declared {opcode op} (hmap : saturatingMeaning opcode = some op) (refs : List funcidx) :
    Spec.DeclaredReferences.Instruction refs op.instruction := by
  unfold saturatingMeaning at hmap
  split at hmap <;> simp only [Option.some.injEq, reduceCtorEq] at hmap <;> try contradiction
  all_goals subst op; simp [i32TruncSatF32S, i32TruncSatF32U, i32TruncSatF64S, i32TruncSatF64U,
    i64TruncSatF32S, i64TruncSatF32U, i64TruncSatF64S, i64TruncSatF64U,
    Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

end Itasca.Body.NumericExtensions

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

namespace Itasca.Body.Simd

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

/-- A lane operation with a byte lane index is well formed. -/
theorem LaneOperation.well_formed (op : LaneOperation) (lane : laneidx) (h : wf_uN 8 lane) :
    wf_instr (op.instruction lane) := by
  cases op <;> simp only [instruction, shape, replace, extension, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first | exact h | decide | constructor

/-- A lane operation with an in-range lane index has its stack effect under `Instr_ok`. -/
theorem LaneOperation.typed (op : LaneOperation) (C : context) (lane : laneidx)
    (hC : wf_context C) (h8 : wf_uN 8 lane) (hl : proj_uN_0 lane < op.count) :
    Instr_ok C (op.instruction lane)
      (.mk_functype (.mk_list op.inputs) (.mk_list op.outputs)) := by
  have hw := op.well_formed lane h8
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
    Spec.DeclaredReferences.Instruction refs (op.instruction lane) := by
  cases op <;> simp [instruction, replace, WebAssembly.Binary.Simd.LaneOperation.instruction,
    WebAssembly.Binary.Simd.LaneOperation.replace, Spec.DeclaredReferences.Instruction,
    Spec.DeclaredReferences.instructionIndices]

end Itasca.Body.Simd

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

namespace Itasca.Body.Simd

/-- A memory operation with a well-formed memory argument and byte lane index is well formed. -/
theorem MemoryOperation.well_formed (op : MemoryOperation) (arg : memarg) (lane : laneidx)
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
  have hw := op.well_formed arg lane ha h8
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
    exact Instr_ok.vload_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load16Lane =>
    exact Instr_ok.vload_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load32Lane =>
    exact Instr_ok.vload_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case load64Lane =>
    exact Instr_ok.vload_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store8Lane =>
    exact Instr_ok.vstore_lane C 8 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store16Lane =>
    exact Instr_ok.vstore_lane C 16 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store32Lane =>
    exact Instr_ok.vstore_lane C 32 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
  case store64Lane =>
    exact Instr_ok.vstore_lane C 64 arg lane mt hm he (by convert halign using 1; norm_num [naturalAlign, size]) (by have h := hlane (by decide); norm_num [laneCount, WebAssembly.Binary.Simd.MemoryOperation.laneCount] at h ⊢; exact_mod_cast h) hC hmt hw
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
    Spec.DeclaredReferences.Instruction refs (op.instruction arg lane) := by
  cases op <;> simp [instruction, WebAssembly.Binary.Simd.MemoryOperation.instruction, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

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

end Itasca.Body.Simd

end

/-! ## DeclaredReferences -/

section

/-!
# Declared references in Wasm 2.0 syntax

Transfers the `C.refs` condition of `Spec/Spec.DeclaredReferences` to flat tokens: `Emits.declared_iff`
and `BodyTokens.declared_iff` show that `TokensDeclared` holds exactly when the spelled
instructions meet `Spec.DeclaredReferences.Instructions`.
-/

namespace Itasca.Body

@[simp] theorem tokens_declared_nil (refs : List funcidx) : TokensDeclared refs [] := by
  simp [TokensDeclared]

@[simp] theorem tokens_declared_append (refs : List funcidx) (a b : List Token) :
    TokensDeclared refs (a ++ b) ↔ TokensDeclared refs a ∧ TokensDeclared refs b := by
  simp [TokensDeclared, or_imp, forall_and]

@[simp] theorem tokens_declared_singleton (refs : List funcidx) (token : Token) :
    TokensDeclared refs [token] ↔ token.Declared refs := by
  simp [TokensDeclared]

@[simp] theorem tokens_declared_cons (refs : List funcidx) (token : Token) (tokens : List Token) :
    TokensDeclared refs (token :: tokens) ↔ token.Declared refs ∧ TokensDeclared refs tokens := by
  simp [TokensDeclared, or_imp, forall_and]

/-- Tokens meet their obligations exactly when the instructions they spell do. -/
theorem Emits.declared_iff {tokens ops} (h : Emits tokens ops) (refs : List funcidx) :
    TokensDeclared refs tokens ↔ Spec.DeclaredReferences.Instructions refs ops := by
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
    TokensDeclared refs tokens ↔ Spec.DeclaredReferences.Instructions refs ops := by
  obtain ⟨inner, rfl, he⟩ := h
  simpa [Token.Declared] using Emits.declared_iff he refs

end Itasca.Body

end

end DeclaredReferences

end

/-! ## Encoding -/

section

/-!
# Encoding

Independent instruction spellings compose into complete structured body encodings. Syntax reconstruction, SIMD bit meanings and uniqueness connect the token grammar to exact instruction trees.
-/

/-! ## Simd -/

section

/-!
# Wasm 2.0 SIMD instruction bytes

`Simd.Immediate` relates a `0xfd` subopcode to its SpecTec instruction and immediate bytes. It
covers pure, lane, memory and lane-memory operations from the public opcode tables,
and the `v128.const` and `i8x16.shuffle` forms. The operation tables retain well-formed
source instructions; `Immediate.prefix_unique` shows that bytes determine the instruction.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- `unpackBytes` returns `count` bytes. -/
theorem unpack_bytes_length (bits count : Nat) : (unpackBytes bits count).length = count := by
  induction count generalizing bits with
  | zero => rfl
  | succ n ih => simp [unpackBytes, ih]

/-- Unpacked bytes are below 256. -/
theorem unpack_bytes_lt (bits count : Nat) : ∀ b ∈ unpackBytes bits count, b < 256 := by
  induction count generalizing bits with
  | zero => simp [unpackBytes]
  | succ n ih =>
    intro b hb
    simp only [unpackBytes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ hb

/-- A vector constant is well formed. -/
theorem vector_constant_wf (low high : U64) : wf_instr (vectorConstant low high) := by
  apply wf_instr.instr_case_20
  · decide
  · constructor
    have hlo : low.val ≤ 18446744073709551615 := by scalar_tac
    have hhi : high.val ≤ 18446744073709551615 := by scalar_tac
    norm_num [size, valtype_vectype]
    omega

/-- A shuffle is well formed. -/
theorem shuffle_wf (low high : U64) : wf_instr (shuffle low high) := by
  apply wf_instr.instr_case_32
  · apply wf_ishape.ishape_case_0 .I8
    · repeat' first | decide | constructor
    · rfl
  · intro lane hl
    simp only [WebAssembly.Binary.Simd.shuffleIndices, List.mem_map, List.mem_append] at hl
    obtain ⟨n, hn, rfl⟩ := hl
    constructor
    rcases hn with hn | hn
    · have := unpack_bytes_lt _ _ _ hn
      norm_num
      omega
    · have := unpack_bytes_lt _ _ _ hn
      norm_num
      omega
  · exact ⟨rfl, by simp [WebAssembly.Binary.Simd.shuffleIndices, unpack_bytes_length]⟩

end Itasca.Body.Simd

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

open Binary

theorem Immediate.prefix_unique (subopcode : U32) : PrefixUnique (Immediate subopcode) := by
  intro x y a b rest tail hx hy eq
  exact PrefixUnique.of_source (f := id) (WebAssembly.Binary.Simd.Immediate.prefix_unique subopcode.val)
    Function.injective_id (Binary.Source.simdImmediate hx) (Binary.Source.simdImmediate hy) eq

end Itasca.Body.Simd

end

/-! ## Encoding -/

section

/-!
# Wasm 2.0 instruction binary grammar

The handwritten binary grammar of Wasm 2.0 instructions. `Immediate` relates an opcode byte to a
token and its immediate bytes, reusing the scalar plain instructions and adding sign extension,
saturating truncation, reference, bulk memory, SIMD and structured control with `BlockEncoding`
block types. `At`, `Consumed` and `BodyEncoding` place tokens, token runs and complete bodies in a
byte slice, as in `Binary/Body.Scalar/Encoding`. The grammar does not mention validation.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- `BlockDecoded` at a cursor is a `BlockEncoding` over an interval of the input. -/
theorem block_decoded_iff {data pos bt next} :
    BlockDecoded data pos bt next ↔
      ∃ bytes, BlockEncoding bt bytes ∧ Body.Scalar.BytesAt data pos bytes next := by
  simp only [BlockEncoding.reader_form]
  cases bt with
  | Empty | Value _ =>
    constructor
    · rintro ⟨hp, hv, hn⟩
      exact ⟨_, rfl, .byte data pos next _ hp hv hn⟩
    · rintro ⟨bytes, rfl, hs⟩
      have hn : next.val = pos.val + 1 := by simpa using hs.length
      have hp : pos.val < data.length := by have := hs.bound; omega
      refine ⟨hp, ?_, hn⟩
      have hh := congrArg List.head? hs.suffix
      simpa only [List.drop_eq_getElem_cons hp, List.singleton_append,
        List.head?_cons, Option.some.injEq] using hh
  | TypeIndex i =>
    exact ⟨fun ⟨bs, hs, hl, hb, he⟩ => ⟨bs, he, hs, hl, hb⟩,
      fun ⟨bs, he, hs, hl, hb⟩ => ⟨bs, hs, hl, hb, he⟩⟩

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
    (himmediate : Immediate opcode token immediate)
    (hspan : Body.Scalar.BytesAt data pos immediate next) : At data start token next := by
  exact ⟨opcode :: immediate, ⟨opcode, immediate, rfl, himmediate⟩,
    by simpa using (Body.Scalar.BytesAt.byte data start pos opcode hstart hbyte hpos).append hspan⟩

/-- A structured instruction header token from a decoded block type. -/
theorem At.of_block_type {data start pos next opcode token} (bt : signature.BlockType)
    (hstart : start.val < data.length) (hbyte : data.val[start.val] = opcode)
    (hpos : pos.val = start.val + 1)
    (himm : ∀ bytes, BlockEncoding bt bytes → Immediate opcode token bytes)
    (hdecoded : BlockDecoded data pos bt next) : At data start token next := by
  obtain ⟨bytes, he, hs⟩ := block_decoded_iff.mp hdecoded
  exact .of_immediate hstart hbyte hpos (himm bytes he) hs

/-- A scalar plain token is a Wasm 2.0 token. -/
theorem At.plain {data start op next} (h : Body.Scalar.At data start (.plain op) next) :
    At data start (.plain op) next := by
  obtain ⟨bs, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  exact ⟨_, ⟨opcode, imm, rfl, .plain hi⟩, hs⟩

/-- A consumed span is within the input. -/
theorem Consumed.span {data start tokens next} (h : Consumed data start tokens next) :
    start.val ≤ next.val ∧ next.val ≤ data.length := by
  induction h with
  | nil hb => exact ⟨Nat.le_refl _, hb⟩
  | snoc _ ha ih => have := ha.span; omega

/-- Consumed spans compose. -/
theorem Consumed.append {data start middle next first rest}
    (hfirst : Consumed data start first middle) (hrest : Consumed data middle rest next) :
    Consumed data start (first ++ rest) next := by
  induction hrest with
  | nil _ => simpa using hfirst
  | snoc _ ha ih => simpa [List.append_assoc] using Consumed.snoc ih ha

end Itasca.Body

end

/-! ## SyntaxComplete -/

section

/-!
# Instruction-by-instruction view of Wasm 2.0 syntax

`Atom` gives the complete token spelling of one instruction, and `Spells` is the left-to-right
form of `Emits`. `Emits.cons_iff` splits the next instruction and its tokens, including nested
delimiters, off the remaining syntax.
-/

namespace Itasca.Body

/-- A single instruction retains the same token derivation as a whole body. -/
abbrev Atom (tokens : List Token) (op : instr) := Emits tokens [op]

/-- Split a right-growing derivation into successive single-instruction spans. -/
private abbrev Spells := WebAssembly.Binary.Rep (fun op tokens => Atom tokens op)

private theorem spells_append {xs ys ops rest} (hx : Spells ops xs) (hy : Spells rest ys) :
    Spells (ops ++ rest) (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons h _ ih => simpa [List.append_assoc] using WebAssembly.Binary.Rep.cons (R := fun op ts => Atom ts op) h ih

private theorem emits_spells {tokens ops} (h : Emits tokens ops) : Spells ops tokens := by
  have one {op ts} (h : Emits ts [op]) : Spells [op] ts := by
    simpa using WebAssembly.Binary.Rep.cons (R := fun op ts => Atom ts op) h .nil
  induction h with
  | nil => exact .nil
  | simple _ hs ih => exact spells_append ih (one (.simple .nil hs))
  | block bt _ hb ih _ => simpa [List.append_assoc] using spells_append ih (one (.block bt .nil hb))
  | loop bt _ hb ih _ => simpa [List.append_assoc] using spells_append ih (one (.loop bt .nil hb))
  | ifElse bt _ hy hn ih _ _ => simpa [List.append_assoc] using spells_append ih (one (.ifElse bt .nil hy hn))
  | ifEnd bt _ hb ih _ => simpa [List.append_assoc] using spells_append ih (one (.ifEnd bt .nil hb))

private theorem spells_emits {tokens ops} (h : Spells ops tokens) : Emits tokens ops := by
  induction h with
  | nil => exact .nil
  | cons hop _ ih => exact Emits.append hop ih

theorem Emits.empty_iff {tokens} : Emits tokens [] ↔ tokens = [] := by
  constructor
  · intro h
    cases emits_spells h
    rfl
  · rintro rfl
    exact .nil

theorem Atom.nonempty {tokens op} (h : Atom tokens op) : tokens ≠ [] := by
  change Emits tokens [op] at h
  generalize eq : [op] = ops at h
  cases h <;> simp_all

/-- Splits off the first instruction without changing its nested delimiters. -/
theorem Emits.cons_iff {tokens op ops} :
    Emits tokens (op :: ops) ↔
      ∃ first rest, tokens = first ++ rest ∧ Atom first op ∧ Emits rest ops := by
  constructor
  · intro h
    cases emits_spells h with
    | cons hop ht => exact ⟨_, _, rfl, hop, spells_emits ht⟩
  · rintro ⟨first, rest, rfl, hop, ht⟩
    exact Emits.append hop ht

end Itasca.Body

end

/-! ## EncodingComplete -/

section

/-!
# Reading Wasm 2.0 encodings

Splitting lemmas for the Wasm 2.0 `At` and `Consumed` relations, as in
`Binary/Body.Scalar/Encoding`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

/-- A token interval is its opcode byte at the cursor followed by an immediate span. -/
theorem At.immediate {data start token next} (h : At data start token next)
    (pos : Usize) (hpos : pos.val = start.val + 1) :
    ∃ opcode immediate, Immediate opcode token immediate ∧
      (∃ hp : start.val < data.length, data.val[start.val] = opcode) ∧
      Body.Scalar.BytesAt data pos immediate next := by
  obtain ⟨_, ⟨opcode, imm, rfl, hi⟩, hs⟩ := h
  have hl := hs.length
  have hb := hs.bound
  simp only [List.length_cons] at hl
  have hp : start.val < data.length := by omega
  have heq := hs.suffix
  rw [List.drop_eq_getElem_cons hp] at heq
  refine ⟨opcode, imm, hi, ⟨hp, (List.cons.inj heq).1⟩, ?_⟩
  exact ⟨by simpa [hpos] using (List.cons.inj heq).2, by omega, hb⟩

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

end Itasca.Body

end

/-! ## SimdBitsMeaning -/

section

/-!
# Typing and declared references of SIMD constants

Shows that `v128.const` and `i8x16.shuffle` have the expected `Instr_ok` typing
(`vector_constant_typed`, `shuffle_typed`), that a generated typing fixes their stack effect
(`vector_constant_principal`, `shuffle_principal`, `shuffle_bound`), and that they carry no
`ref.func`. `shuffle_indices_encoding` relates the lane indices to the immediate bytes.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body.Simd

/-- A vector constant has type `[] -> [v128]`. -/
theorem vector_constant_typed (C : context) (low high : U64) (hC : wf_context C) :
    Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list []) (.mk_list [.V128])) :=
  .vconst C _ hC (vector_constant_wf low high)

/-- A generated typing of a vector constant has the stack effect `[] -> [v128]`. -/
theorem vector_constant_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (vectorConstant low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

/-- Unpacking the value of a byte list recovers the bytes. -/
theorem unpack_bytes_payload (bytes : List U8) :
    unpackBytes (Binary.FloatBits.payload bytes) bytes.length = bytes.map UScalar.val := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [Binary.FloatBits.payload_nil, Binary.FloatBits.payload_cons, List.length_cons, unpackBytes, List.map_cons]
    have hm : (b.val + 256 * Binary.FloatBits.payload bs) % 256 = b.val := by omega
    have hd : (b.val + 256 * Binary.FloatBits.payload bs) / 256 = Binary.FloatBits.payload bs := by omega
    rw [hm, hd, ih]

/-- The lane indices of a shuffle are the bytes of its two immediate halves. -/
theorem shuffle_indices_encoding (low high : U64) (lower upper : List U8)
    (hl : Binary.FloatBits.Encoding 8 lower low.val) (hh : Binary.FloatBits.Encoding 8 upper high.val) :
    shuffleIndices low high = (lower ++ upper).map (fun b => uN.mk_uN b.val) := by
  have hlo : unpackBytes low.val 8 = lower.map UScalar.val := by
    rw [hl.2, ← hl.1, unpack_bytes_payload]
  have hhi : unpackBytes high.val 8 = upper.map UScalar.val := by
    rw [hh.2, ← hh.1, unpack_bytes_payload]
  simp [shuffleIndices, hlo, hhi, List.map_append, List.map_map, Function.comp_def]

/-- A shuffle with lane indices below 32 has type `[v128, v128] -> [v128]`. -/
theorem shuffle_typed (C : context) (low high : U64) (hC : wf_context C)
    (hl : ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32) :
    Instr_ok C (shuffle low high)
      (.mk_functype (.mk_list [.V128, .V128]) (.mk_list [.V128])) := by
  exact .vshuffle C _ _ (.mk_dim 16) (by constructor; constructor; decide)
    hl hC (by constructor; decide) (shuffle_wf low high)

/-- A generated typing of a shuffle has the stack effect `[v128, v128] -> [v128]`. -/
theorem shuffle_principal (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ins = [.V128, .V128] ∧ outs = [.V128] := by cases ht; exact ⟨rfl, rfl⟩

/-- A generated typing of a shuffle bounds every lane index by 32. -/
theorem shuffle_bound (C : context) (low high : U64) (ins outs : List valtype)
    (ht : Instr_ok C (shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs))) :
    ∀ lane ∈ shuffleIndices low high, proj_uN_0 lane < 32 := by
  cases ht
  cases_type fun_dim
  assumption

/-- A vector constant has no declared-reference obligation. -/
theorem vector_constant_declared (refs : List funcidx) (low high : U64) :
    Spec.DeclaredReferences.Instruction refs (vectorConstant low high) := by
  simp [vectorConstant, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

/-- A shuffle has no declared-reference obligation. -/
theorem shuffle_declared (refs : List funcidx) (low high : U64) :
    Spec.DeclaredReferences.Instruction refs (shuffle low high) := by
  simp [shuffle, Spec.DeclaredReferences.Instruction, Spec.DeclaredReferences.instructionIndices]

end Itasca.Body.Simd

end

/-! ## SyntaxUnique -/

section

/-!
# Uniqueness of Wasm 2.0 instruction syntax

`Emits.unique` and `BodyTokens.unique` show that a token list spells at most one instruction
list. The structured decoding proof lives in `WebAssembly.Binary.SyntaxUnique`.
-/

namespace Itasca.Body

/-- A token list determines the structured instructions it spells. -/
theorem Emits.unique {tokens xs ys} (hx : Emits tokens xs) (hy : Emits tokens ys) : xs = ys :=
  (Binary.Source.emits hx).unique (Binary.Source.emits hy)

/-- A body's tokens determine its instructions. -/
theorem BodyTokens.unique {tokens xs ys}
    (hx : BodyTokens tokens xs) (hy : BodyTokens tokens ys) : xs = ys :=
  (Binary.Source.bodyTokens hx).unique (Binary.Source.bodyTokens hy)

end Itasca.Body

end

end
