import Exec.Code.Local.Relations.Common.ReaderOpcode
import Itasca.Wasm2.Step.Dispatch
import Itasca.Wasm2.NumericExt.Dispatch
import Itasca.Handler.NumericDispatch
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
    ReaderOpcode .Wasm1 opcode ∨
    code.step visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : ReaderOpcode .Wasm1 opcode
  · exact .inl supported
  right
  by_cases high : 69 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode value high]
    cases meaning : Numeric.opcodeMeaning opcode with
    | none => exact code.step_numeric.unrecognized visitor st opcode value meaning
    | some operation => exact False.elim (supported (numeric_reader_opcode meaning))
  · apply code.step.reserved
    rcases opcode with ⟨⟨index,bound⟩⟩
    change ¬ 69 ≤ index at high
    have upper : index ≤ 68 := by omega
    interval_cases index <;> first | (exfalso; apply supported; reader_opcode) | (clear supported; decide +revert)

/-- Extension dispatch likewise rejects every opcode outside the executable
profile, independently of the reader or visitor state. -/
theorem reader_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    ReaderOpcode .Wasm2 opcode ∨
    code.step_wasm2 visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : ReaderOpcode .Wasm2 opcode
  · exact .inl supported
  right
  have base : opcode.val ∉ [28,37,38,208,209,210,252,253] := by
    intro member
    rcases opcode with ⟨⟨index,bound⟩⟩
    change index ∈ _ at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    apply supported
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reader_opcode
  have sign : Wasm2.NumericExtensions.signMeaning opcode = none := by
    cases meaning : Wasm2.NumericExtensions.signMeaning opcode with
    | none => rfl
    | some operation => exact False.elim (supported (sign_reader_opcode meaning))
  have misc : opcode ≠ code.OP_MISC_PREFIX := fun equal => supported (.misc (by simpa [code.OP_MISC_PREFIX] using equal))
  rw [code.step_wasm2.base visitor st data env ctx opcode value base,
    code.step_extended.base visitor st data env ctx opcode value sign misc]
  rcases reader_opcode_wasm1 visitor st data env ctx opcode value with known | rejected
  · exact False.elim (supported known.wasm2)
  · exact rejected

theorem reader_accepted_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (typeIndex : U32) (opcode : U8) (value after : V)
    (accepted : code.step_profile visitor st data env ctx typeIndex .Wasm2 opcode value =
      .ok (.Ok (),final,after)) : ReaderOpcode .Wasm2 opcode := by
  by_contra unknown
  have rejected := (reader_opcode_wasm2 visitor st.core data env ctx opcode value).resolve_left unknown
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  unfold code.step_profile at accepted
  simp only [code.check_opcode, bind_ok, hok] at accepted
  split at accepted
  all_goals try { exfalso; apply unknown; reader_opcode }
  all_goals
    split at accepted
    · simp at accepted
    · simp [rejected,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
end Exec.Code
