import Itasca.Runtime.Compiler.Body.Reader.Acceptance.RecordedAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchAndScopeEffects
import Itasca.Runtime.Compiler.Body.Reader.Safety.InstructionSafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Body.Bulk.Step

/-!
Proofs for Runtime / Compiler / Body / Reader / Source.

This module collects SourceOpcodeDescriptors, SourceOpcodeFamilies.
Each section documents its contracts and consumers.
-/

/-! ## SourceOpcodeDescriptors -/

section

/-!
# Source opcode descriptors

Numeric, memory, sign-extension and saturating opcode partitions produce canonical source descriptors. Reader acceptance uses this independent classification.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 8192

theorem source_numeric_byte_partition (opcode : U8) (lower : 69 ≤ opcode.val)
    (upper : opcode.val < 192) :
    opcode ∈ integerOpcodes ∨ opcode.val ∈ floatBaseOpcodeValues := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 69 ≤ n at lower
  change n < 192 at upper
  interval_cases n <;> decide +revert

theorem source_memory_byte_partition (opcode : U8) (lower : 40 ≤ opcode.val)
    (upper : opcode.val ≤ 62) :
    (∃ op : SourceMachine.Memory.Load, UScalar.cast .U8 (memoryLoadOpcode op) = opcode) ∨
    (∃ op : SourceMachine.Memory.Store, UScalar.cast .U8 (memoryStoreOpcode op) = opcode) := by
  interval_cases h : opcode.val
  · exact Or.inl ⟨.full .I32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .I64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .F32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.full .F64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .byte .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .byte .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .half .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I32 .half .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .byte .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .byte .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .half .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .half .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .word .S, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inl ⟨.packed .I64 .word .U, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .I32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .I64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .F32, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.full .F64, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I32 .byte, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I32 .half, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .byte, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .half, (UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact Or.inr ⟨.packed .I64 .word, (UScalar.eq_equiv _ _).mpr h.symm⟩

theorem source_sign_byte_descriptor (opcode : U8) (lower : 192 ≤ opcode.val)
    (upper : opcode.val ≤ 196) :
    ∃ op : SourceMachine.Numeric.Instruction, 192 ≤ (integerOpcode op).val ∧
      UScalar.cast .U8 (integerOpcode op) = opcode := by
  interval_cases h : opcode.val
  · exact ⟨.unary .I32 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I32 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend8,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend16,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩
  · exact ⟨.unary .I64 .extend32,by decide,(UScalar.eq_equiv _ _).mpr h.symm⟩

theorem source_saturating_descriptor (opcode : U32) (small : opcode.val < 8) :
    ∃ op : SourceMachine.Float.Instruction, 256 ≤ (floatOpcode op).val ∧
      opcode.val = (floatOpcode op).val - 256 := by
  interval_cases h : opcode.val
  · exact ⟨.truncate .F32 .I32 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I32 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I32 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I32 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I64 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F32 .I64 .U true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I64 .S true,by decide,rfl⟩
  · exact ⟨.truncate .F64 .I64 .U true,by decide,rfl⟩

end Itasca.Compiler

end

/-! ## SourceOpcodeFamilies -/

section

/-! ## SourceMiscPrefix -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Independent accepted bulk dispatch excludes every unsupported subopcode. -/
theorem source_bulk_supported {V : Type} (source : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env) (sub : U32) (before after : V)
    (reference : code.step_bulk source st data env sub before = .ok (.Ok (),out,after)) :
    sub.val ∈ [8,9,10,11,12,13,14,15,16,17] := by
  rw [code.step_bulk.eq_runs] at reference
  unfold Body.bulkStep at reference
  split at reference <;> first | decide | simp_all

/-- An accepted miscellaneous prefix has an independently decoded saturating
or bulk subopcode. Decode failure and unsupported bulk cases are excluded by
the source run itself, without any compiler premise. -/
theorem source_misc_prefix {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (before after : V)
    (reference : code.step_profile source st data env ctx index 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ sub next, Binary.Leb128.Decoded data st.core.pos sub next ∧
      (sub.val < 8 ∨ sub.val ∈ [8,9,10,11,12,13,14,15,16,17]) := by
  obtain ⟨capacity,raw⟩ := scalar_success source st out data env ctx index 252#u8 before after (by decide) reference
  rw [code.step_wasm2.prefixed] at raw
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Body.miscellaneousStep,read,bind_ok] at raw
  cases result with
  | Err error => simp at raw
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    refine ⟨sub,next,decoded,?_⟩
    by_cases small : sub < 8#u32
    · exact .inl (by scalar_tac)
    · simp only [small,↓reduceIte] at raw
      exact .inr (source_bulk_supported source _ out.core data env sub before after raw)

end Itasca.Compiler

end

/-! ## SourceOpcodeFamilies -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 8192

/-- Base dispatcher rejection after all supported instruction extensions have
been excluded. The two ranges correspond to reserved low bytes and absent
base numeric rows. -/
structure ReservedSourceOpcode (opcode : U8) : Prop where
  absent : ((6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨ (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
    (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨ (37 ≤ opcode.val ∧ opcode.val ≤ 39)) ∨ 192 ≤ opcode.val
  ordinary : opcode.val ∉ Body.controlOpcodes
  plain : opcode.val ∉ [28,37,38,208,209,210,252,253]
  sign : Body.NumericExtensions.signMeaning opcode = none
  misc : opcode ≠ code.OP_MISC_PREFIX

/-- Source opcode coverage for complete acceptance. Numeric and memory
cases retain their checked descriptor, while reserved bytes retain rejection
premises independently of any compiler result. -/
inductive SourceOpcodeFamily (opcode : U8) : Prop where
  | scalar (kind : ScalarReaderKind) : opcode = kind.opcode → SourceOpcodeFamily opcode
  | control (kind : ControlReaderKind) : opcode = kind.opcode → SourceOpcodeFamily opcode
  | table : opcode = 14#u8 → SourceOpcodeFamily opcode
  | typedSelect : opcode = 28#u8 → SourceOpcodeFamily opcode
  | integer (op : SourceMachine.Numeric.Instruction) : (integerOpcode op).val < 192 →
      opcode = UScalar.cast .U8 (integerOpcode op) → SourceOpcodeFamily opcode
  | float (op : SourceMachine.Float.Instruction) : (floatOpcode op).val < 256 →
      opcode = UScalar.cast .U8 (floatOpcode op) → SourceOpcodeFamily opcode
  | sign (op : SourceMachine.Numeric.Instruction) : 192 ≤ (integerOpcode op).val →
      opcode = UScalar.cast .U8 (integerOpcode op) → SourceOpcodeFamily opcode
  | load (op : SourceMachine.Memory.Load) : opcode = UScalar.cast .U8 (memoryLoadOpcode op) → SourceOpcodeFamily opcode
  | store (op : SourceMachine.Memory.Store) : opcode = UScalar.cast .U8 (memoryStoreOpcode op) → SourceOpcodeFamily opcode
  | stateful : opcode.val ∈ [37,38,63,64,208,209,210] → SourceOpcodeFamily opcode
  | misc : opcode = 252#u8 → SourceOpcodeFamily opcode
  | simd : opcode = 253#u8 → SourceOpcodeFamily opcode
  | reserved : ReservedSourceOpcode opcode → SourceOpcodeFamily opcode

private def scalarKinds : List ScalarReaderKind :=
  [.nop,.unreachable,.drop,.select,.local_get,.local_set,.local_tee,.global_get,.global_set,
    .i32_const,.i64_const,.f32_const,.f64_const]
private def controlKinds : List ControlReaderKind :=
  [.block,.loop,.if_,.else_,.end_,.br,.br_if,.return_,.call,.call_indirect]

/-- Checked exhaustive classification of every byte, with no target execution
or accepted target trace involved. -/
theorem source_opcode_family (opcode : U8) : SourceOpcodeFamily opcode := by
  by_cases scalar : opcode.val ∈ scalarKinds.map (fun kind => kind.opcode.val)
  · obtain ⟨kind,_,same⟩ := List.mem_map.mp scalar
    exact .scalar kind (UScalar.eq_of_val_eq same.symm)
  by_cases control : opcode.val ∈ controlKinds.map (fun kind => kind.opcode.val)
  · obtain ⟨kind,_,same⟩ := List.mem_map.mp control
    exact .control kind (UScalar.eq_of_val_eq same.symm)
  by_cases table : opcode.val = 14
  · exact .table (UScalar.eq_of_val_eq table)
  by_cases typed : opcode.val = 28
  · exact .typedSelect (UScalar.eq_of_val_eq typed)
  by_cases memory : 40 ≤ opcode.val ∧ opcode.val ≤ 62
  · rcases source_memory_byte_partition opcode memory.1 memory.2 with ⟨op,same⟩ | ⟨op,same⟩
    · exact .load op same.symm
    · exact .store op same.symm
  by_cases numeric : 69 ≤ opcode.val ∧ opcode.val < 192
  · rcases source_numeric_byte_partition opcode numeric.1 numeric.2 with integer | float
    · obtain ⟨op,same⟩ := integer_opcode_of_mem integer
      have bounded := integer_opcode_byte op
      have base : (integerOpcode op).val < 192 := by
        have values := congrArg UScalar.val same
        scalar_tac
      exact .integer op base same.symm
    · obtain ⟨op,base,same⟩ := float_base_opcode_of_mem float
      exact .float op base same.symm
  by_cases sign : 192 ≤ opcode.val ∧ opcode.val ≤ 196
  · obtain ⟨op,extension,same⟩ := source_sign_byte_descriptor opcode sign.1 sign.2
    exact .sign op extension same.symm
  by_cases stateful : opcode.val ∈ [37,38,63,64,208,209,210]
  · exact .stateful stateful
  by_cases misc : opcode.val = 252
  · exact .misc (UScalar.eq_of_val_eq misc)
  by_cases simd : opcode.val = 253
  · exact .simd (UScalar.eq_of_val_eq simd)
  norm_num [scalarKinds,ScalarReaderKind.opcode,global_simps] at scalar
  norm_num [controlKinds,ControlReaderKind.opcode] at control
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at stateful
  have ordinary : opcode.val ∉ Body.controlOpcodes := by
    simp only [Body.controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or]
    tauto
  have plain : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    tauto
  have noSign : Body.NumericExtensions.signMeaning opcode = none := by
    unfold Body.NumericExtensions.signMeaning
    split <;> simp_all
  have noMisc : opcode ≠ code.OP_MISC_PREFIX := by
    intro equal
    have values := congrArg UScalar.val equal
    simp only [global_simps] at values
    exact misc values
  exact .reserved ⟨by omega,ordinary,plain,noSign,noMisc⟩

/-- Independently accepted source validation excludes every reserved family. -/
theorem ReservedSourceOpcode.rejects {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (before after : V) (reserved : ReservedSourceOpcode opcode)
    (reference : code.step_profile source st data env ctx index opcode before = .ok (.Ok (),out,after)) : False := by
  obtain ⟨_,raw⟩ := base_success source st out data env ctx ctx index opcode before after
    reserved.ordinary reserved.plain reserved.sign reserved.misc rfl reference
  rcases reserved.absent with low | high
  · rw [code.step.reserved source st.core data env ctx opcode before low] at raw
    simp at raw
  · have absent : Body.Numeric.opcodeMeaning opcode = none := by
      cases meaning : Body.Numeric.opcodeMeaning opcode with
      | none => rfl
      | some operation =>
        have bounded := Body.Numeric.NumericOp.bounds meaning
        omega
    rw [code.step.numeric_dispatch source st.core data env ctx opcode before (by omega),
      code.step_numeric.unrecognized source st.core opcode before absent] at raw
    simp at raw

end Itasca.Compiler

end

end
