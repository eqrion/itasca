import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Wasm2.Step.Dispatch
import Itasca.Wasm2.NumericExt.Dispatch
import Itasca.Handler.Select
import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Reader.Calls.Instructions
import Itasca.Runtime.Compiler.Body.Reader.Replay.BulkAndSaturatingAcceptance

/-!
Sections, each formerly its own module: OpcodeClassification, BodySafety, ProfileSafety.
-/

/-! ## OpcodeClassification -/

section

/-!
An unrecognized base opcode rejects before visiting the compiler.

Main declarations: `reader_opcode_base` and `reader_accepted_opcode_wasm2`. A direct consumer is `Compiler.Body.Reader.Replay.OrdinaryLedger`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- An unrecognized base opcode rejects before visiting the compiler. -/
theorem reader_opcode_base {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    BaseOpcode opcode ∨
    code.step visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : BaseOpcode opcode
  · exact .inl supported
  right
  by_cases high : 69 ≤ opcode.val
  · rw [code.step.numeric_dispatch visitor st data env ctx opcode value high]
    cases meaning : Numeric.opcodeMeaning opcode with
    | none => exact code.step_numeric.unrecognized visitor st opcode value meaning
    | some operation => exact False.elim (supported (numeric_base_opcode meaning))
  · apply code.step.reserved
    rcases opcode with ⟨⟨index,bound⟩⟩
    change ¬ 69 ≤ index at high
    have upper : index ≤ 68 := by omega
    interval_cases index <;> first | (exfalso; apply supported; reader_opcode) | (clear supported; decide +revert)

/-- Extension dispatch likewise rejects every opcode outside the executable
profile, independently of the reader or visitor state. -/
theorem reader_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (opcode : U8) (value : V) :
    ReaderOpcode opcode ∨
    code.step_wasm2 visitor st data env ctx opcode value =
      .ok (.Err error.OpError.UnrecognizedOpcode,st,value) := by
  by_cases supported : ReaderOpcode opcode
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
  rcases reader_opcode_base visitor st data env ctx opcode value with known | rejected
  · exact False.elim (supported known.reader)
  · exact rejected

theorem reader_accepted_opcode_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st final : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (typeIndex : U32) (opcode : U8) (value after : V)
    (accepted : code.step_profile visitor st data env ctx typeIndex opcode value =
      .ok (.Ok (),final,after)) : ReaderOpcode opcode := by
  by_contra unknown
  have rejected := (reader_opcode_wasm2 visitor st.core data env ctx opcode value).resolve_left unknown
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  unfold code.step_profile at accepted
  simp only [bind_ok, hok] at accepted
  split at accepted
  all_goals try { exfalso; apply unknown; reader_opcode }
  all_goals
    split at accepted
    · simp at accepted
    · simp [rejected,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at accepted
end Itasca.Runtime.Compiler

end

/-! ## BodySafety -/

section

/-!
Body-state readers invoke the compiler only after their actual successful parse and validation result. Rejections on either side return normally.

Main declarations: `reader_body_run_reached`. A direct consumer is `Compiler.Body.Reader.Calls.Safety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.VisitorTrace

/-- Body-state readers invoke the compiler only after their actual successful
parse and validation result. Rejections on either side return normally. -/
theorem reader_body_run_reached {T V : Type}
    (read : Result (core.result.Result T error.OpError × code.BodyState))
    (visitor : code.OpVisitor V) (action : T → Action)
    (before : V) (post : code.BodyState → V → Prop)
    (reader : read ⦃ _ => True ⦄)
    (callback : ∀ state value, read = .ok (.Ok value,state) →
      invoke visitor before (.op state.core (action value)) ⦃ out => out.1 = .Ok () → post state out.2 ⦄) :
    CallbackTrace.bodyRun read visitor action before ⦃ out =>
      out.1 = .Ok () → post out.2.1 out.2.2 ⦄ := by
  obtain ⟨⟨result,state⟩,readEq,_⟩ := WP.spec_imp_exists reader
  cases result with
  | Err error => simp [CallbackTrace.bodyRun,readEq]
  | Ok value =>
    obtain ⟨⟨result,after⟩,called,ready⟩ := WP.spec_imp_exists (callback state value readEq)
    cases result with
    | Err error => simp [CallbackTrace.bodyRun,readEq,called,hookResult]
    | Ok unitValue =>
      cases unitValue
      simpa [CallbackTrace.bodyRun,readEq,called,hookResult,WP.spec_ok] using ready rfl
end Itasca.Runtime.Compiler

end

/-! ## ProfileSafety -/

section

/-!
The actual profile capacity guard is checked before ordinary decoding. Only the non-full branch needs the corresponding scalar-reader theorem.

Main declarations: `reader_profile_scalar_reached`. A direct consumer is `Compiler.Body.Reader.Safety.ProfileOrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual profile capacity guard is checked before ordinary decoding.
Only the non-full branch needs the corresponding scalar-reader theorem. -/
theorem reader_profile_scalar_reached {V} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V) (post : code.OpIterState → V → Prop)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (step : st.core.vals.val.length < Usize.max →
      code.step_wasm2 visitor st.core data env ctx opcode before ⦃ out =>
        out.1 = .Ok () → post out.2.1 out.2.2 ⦄) :
    code.step_profile visitor st data env ctx index opcode before ⦃ out =>
      out.1 = .Ok () → post out.2.1.core out.2.2 ⦄ := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary]
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full]
  · rw [if_neg full]
    have capacity : st.core.vals.val.length < Usize.max := by
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega
    obtain ⟨⟨reply,state,after⟩,run,success⟩ := WP.spec_imp_exists (step capacity)
    rw [run]
    cases reply with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unitValue =>
      cases unitValue
      simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Std.uncurry,WP.spec_ok] using success
end Itasca.Runtime.Compiler

end
