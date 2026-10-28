import Itasca.Runtime.Code.Body.Reader.Source.SourceOpcodeDescriptors

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 8192

/-- Base dispatcher rejection after all supported profile extensions have
been excluded. The two ranges correspond to reserved low bytes and absent
base numeric rows. -/
structure ReservedSourceOpcode (opcode : U8) : Prop where
  absent : ((6 ≤ opcode.val ∧ opcode.val ≤ 10) ∨ (18 ≤ opcode.val ∧ opcode.val ≤ 25) ∨
    (28 ≤ opcode.val ∧ opcode.val ≤ 31) ∨ (37 ≤ opcode.val ∧ opcode.val ≤ 39)) ∨ 192 ≤ opcode.val
  ordinary : opcode.val ∉ Wasm2.controlOpcodes
  plain : opcode.val ∉ [28,37,38,208,209,210,252,253]
  sign : Wasm2.NumericExtensions.signMeaning opcode = none
  misc : opcode ≠ code.OP_MISC_PREFIX

/-- Source opcode coverage for complete-profile acceptance. Numeric and memory
cases retain their checked descriptor, while reserved bytes retain rejection
premises independently of any compiler result. -/
inductive SourceOpcodeFamily (opcode : U8) : Prop where
  | scalar (kind : ScalarReaderKind) : opcode = kind.opcode → SourceOpcodeFamily opcode
  | control (kind : ControlReaderKind) : opcode = kind.opcode → SourceOpcodeFamily opcode
  | table : opcode = 14#u8 → SourceOpcodeFamily opcode
  | typedSelect : opcode = 28#u8 → SourceOpcodeFamily opcode
  | integer (op : Abs.Numeric.Instruction) : (integerOpcode op).val < 192 →
      opcode = UScalar.cast .U8 (integerOpcode op) → SourceOpcodeFamily opcode
  | float (op : Abs.Float.Instruction) : (floatOpcode op).val < 256 →
      opcode = UScalar.cast .U8 (floatOpcode op) → SourceOpcodeFamily opcode
  | sign (op : Abs.Numeric.Instruction) : 192 ≤ (integerOpcode op).val →
      opcode = UScalar.cast .U8 (integerOpcode op) → SourceOpcodeFamily opcode
  | load (op : Abs.Memory.Load) : opcode = UScalar.cast .U8 (memoryLoadOpcode op) → SourceOpcodeFamily opcode
  | store (op : Abs.Memory.Store) : opcode = UScalar.cast .U8 (memoryStoreOpcode op) → SourceOpcodeFamily opcode
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
      have bounded := integerOpcode_byte op
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
  have ordinary : opcode.val ∉ Wasm2.controlOpcodes := by
    simp only [Wasm2.controlOpcodes,List.mem_cons,List.not_mem_nil,or_false,not_or]
    tauto
  have plain : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    tauto
  have noSign : Wasm2.NumericExtensions.signMeaning opcode = none := by
    unfold Wasm2.NumericExtensions.signMeaning
    split <;> simp_all
  have noMisc : opcode ≠ code.OP_MISC_PREFIX := by
    intro equal
    have values := congrArg UScalar.val equal
    simp only [global_simps] at values
    exact misc values
  exact .reserved ⟨by omega,ordinary,plain,noSign,noMisc⟩

/-- Independently accepted source validation excludes every reserved family. -/
theorem ReservedSourceOpcode.rejects {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (opcode : U8) (before after : V) (reserved : ReservedSourceOpcode opcode)
    (reference : code.step_profile source st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) : False := by
  obtain ⟨_,raw⟩ := profile_base_success_wasm2 source st out data env ctx ctx index opcode before after
    reserved.ordinary reserved.plain reserved.sign reserved.misc rfl reference
  rcases reserved.absent with low | high
  · rw [code.step.reserved source st.core data env ctx opcode before low] at raw
    simp at raw
  · have absent : Numeric.opcodeMeaning opcode = none := by
      cases meaning : Numeric.opcodeMeaning opcode with
      | none => rfl
      | some operation =>
        have bounded := Numeric.NumericOp.bounds meaning
        omega
    rw [code.step.numeric_dispatch source st.core data env ctx opcode before (by omega),
      code.step_numeric.unrecognized source st.core opcode before absent] at raw
    simp at raw

end Itasca.Runtime.Code
