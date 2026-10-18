import Exec.Code.Local.Relations.Common.ExecutableWasm1Opcodes
import Itasca.Wasm1.StepScalar
import Itasca.Wasm2.Step.Dispatch
import Itasca.Wasm2.NumericExt.Dispatch
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- An unrecognized base-profile opcode rejects before visiting the compiler. -/
theorem reader_opcode_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    (FloatCoreOpcode opcode ∨ opcode.val ∈ [63,64] ∨ opcode = 17#u8 ∨ opcode = 14#u8) ∨
    code.step visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : FloatCoreOpcode opcode ∨ opcode.val ∈ [63,64] ∨ opcode = 17#u8 ∨ opcode = 14#u8
  · exact Or.inl supported
  right
  by_cases high : 69 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode value high]
    cases meaning : Numeric.opcodeMeaning opcode with
    | none => exact code.step_numeric.unrecognized visitor st opcode value meaning
    | some operation =>
      have bounds := Numeric.NumericOp.bounds meaning
      have known := numeric_executable_opcode meaning
      have core : FloatCoreOpcode opcode := by
        simp only [ExecutableOpcode,CumulativeOpcode] at known
        rcases known with (h | extra | equal) | equal | equal | equal
        · exact h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
          omega
        all_goals subst opcode; simp at bounds
      exact False.elim (supported (.inl core))
  · apply code.step.reserved
    rcases opcode with ⟨⟨index,bound⟩⟩
    change ¬ 69 ≤ index at high
    have upper : index ≤ 68 := by omega
    interval_cases index <;>
      simp_all [FloatCoreOpcode,CoreOpcode,SliceOpcode,floatBaseOpcodeValues,UScalar.val]

/-- Extension dispatch likewise rejects every opcode outside the executable
profile, independently of the reader or visitor state. -/
theorem reader_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    ExecutableOpcode opcode ∨
    code.step_wasm2 visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : ExecutableOpcode opcode
  · exact .inl supported
  right
  have base : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    intro member
    apply supported
    simp only [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode,
      List.mem_cons,List.not_mem_nil,or_false,UScalar.eq_equiv] at *
    simp only [UScalar.val] at *
    tauto
  have sign : Wasm2.NumericExtensions.signMeaning opcode = none := by
    unfold Wasm2.NumericExtensions.signMeaning
    split <;> try rfl
    all_goals apply False.elim; apply supported
    all_goals simp_all [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode]
  have misc : opcode ≠ code.OP_MISC_PREFIX := by
    intro equal
    subst opcode
    exact supported (by simp [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,code.OP_MISC_PREFIX])
  rw [code.step_wasm2.base visitor st data env ctx opcode value base,
    code.step_extended.base visitor st data env ctx opcode value sign misc]
  rcases reader_opcode_wasm1 visitor st data env ctx opcode value with known | rejected
  · apply False.elim; apply supported
    rcases known with core | memory | indirect | table
    · exact .inl (.inl core)
    · exact .inl (.inr (.inl (by simp only [List.mem_cons,List.not_mem_nil,or_false] at memory ⊢; tauto)))
    · exact .inl (.inr (.inr indirect))
    · exact .inr (.inr (.inl table))
  · exact rejected

theorem reader_accepted_opcode_wasm1 {V : Type} (visitor : code.OpVisitor V)
    (st final : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (value after : V)
    (accepted : code.step visitor st data env ctx opcode value = .ok (.Ok (),final,after)) :
    FloatCoreOpcode opcode ∨ opcode.val ∈ [63,64] ∨ opcode = 17#u8 ∨ opcode = 14#u8 := by
  rcases reader_opcode_wasm1 visitor st data env ctx opcode value with supported | rejected
  · exact supported
  · rw [rejected] at accepted
    simp at accepted

theorem reader_accepted_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (typeIndex : U32) (opcode : U8) (value after : V)
    (accepted : code.step_profile visitor st data env ctx typeIndex .Wasm2 opcode value =
      .ok (.Ok (),final,after)) : ExecutableOpcode opcode := by
  by_contra unknown
  have rejected := (reader_opcode_wasm2 visitor st.core data env ctx opcode value).resolve_left unknown
  unfold code.step_profile at accepted
  dsimp only at accepted
  split at accepted
  all_goals try { exact False.elim (unknown (by simp only [ExecutableOpcode,CumulativeOpcode,FloatCoreOpcode,CoreOpcode,SliceOpcode]; decide)) }
  all_goals
    split at accepted
    · simp at accepted
    · simp [rejected,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
end Exec.Code
