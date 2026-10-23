import Exec.Code.Body.Reader.Common.ReaderPopPrefix
import Exec.Code.Local.Relations.Common.KnownPopStack
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.ResultFacts
set_option maxHeartbeats 2000000

/-- The newly opened frame begins at an unchanged prefix of the old raw operands. -/
def EntryPrefix (before after : code.OpIterState) : Prop :=
  ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
    ctrl.value_stack_base.val ≤ after.vals.val.length ∧
    after.vals.val.take ctrl.value_stack_base.val <+: before.vals.val

@[step] theorem enter_params_prefix (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (shape : Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max) :
    enterParams st env form.kind bt ⦃ out => out.1 = .Ok () → EntryPrefix st.core out.2.core ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with pop_results_prefix st.core env (inputs bt) outer segment values base
    as ⟨result, middle, controls, position, rest, middleValues, restPrefix⟩
  have middleShape : Control.Shape middle := shape.replace_operands controls (by simp [base, middleValues])
  step
  split
  · step with code.push_frame.spec {st with core := middle} form.kind bt (by simpa [controls] using capacity)
      as ⟨framed, frameControls, frameValues, framePosition, frameBlocks⟩
    have framedShape := shape_push middleShape form.kind bt frameControls frameValues
    step with code.push_results.total framed.core env (inputs bt) framedShape
      as ⟨reply, final, finalShape, finalControls, finalPosition, pushed⟩
    intro success
    obtain ⟨types, resolved, appended⟩ := pushed success
    refine ⟨middle.ctrls.val, frame middle form.kind bt, ?_, ?_, ?_⟩
    · rw [finalControls, frameControls]
    · simp [Wasm2.frame, alloc.vec.Vec.len, appended, frameValues]
    · simp only [Wasm2.frame, alloc.vec.Vec.len]
      rw [appended, frameValues]
      change (middle.vals.val ++ types.map code.StackType.Val).take middle.vals.val.length <+: st.core.vals.val
      rw [List.take_left]
      rcases restPrefix with ⟨suffix, suffixEq⟩
      exact ⟨suffix, by rw [middleValues, values, ← suffixEq, List.append_assoc]⟩
  · step*

@[step] theorem enter_args_prefix (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (initial : form.Initial)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (shape : Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max) :
    enterArgs st env form.kind bt ⦃ out => out.1 = .Ok () → EntryPrefix st.core out.2.core ⦄ := by
  rcases initial with rfl | rfl | rfl
  · exact enter_params_prefix st env .block bt outer segment values base shape capacity
  · exact enter_params_prefix st env .loop bt outer segment values base shape capacity
  · simp only [enterArgs, Frames.Form.kind]
    step with pop_with_type_prefix st.core outer segment .I32 values base
      as ⟨result, middle, controls, position, rest, middleValues, restPrefix⟩
    step
    split
    · have middleShape := shape.replace_operands controls (by simp [base, middleValues])
      apply WP.spec_mono (enter_params_prefix {st with core := middle} env .then_ bt outer rest middleValues
        (by simpa [Control.base, controls] using base) middleShape (by simpa [controls] using capacity))
      rintro ⟨status,after⟩ effect success
      obtain ⟨prior,ctrl,afterControls,bound,kept⟩ := effect success
      refine ⟨prior,ctrl,afterControls,bound,kept.trans ?_⟩
      rcases restPrefix with ⟨suffix,suffixEq⟩
      exact ⟨suffix, by rw [middleValues,values,← suffixEq,List.append_assoc]⟩
    · step*
end Exec.Code
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.ResultFacts

theorem reader_enter_prefix_wasm2 {data env locals index st out bt} {form : Frames.Form}
    (p : Wasm2.Pending data env .Wasm2 locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env .Wasm2 form.kind = .ok (.Ok bt, out)) :
    EntryPrefix st.core out.core := by
  have erased : code.enter st data env .Wasm2 form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  rw [enter_eq] at erased
  obtain ⟨readResult, readCall, rest⟩ := bind_ok_inv _ _ _ erased
  cases readResult with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok pair =>
    obtain ⟨decoded, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨checked, checkCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases checked with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨C, outer, spine, header, position, typed, controls, blocks, values⟩ := p.opened
      have base : (Control.base st.core).val = outer.length := by simp [Control.base, controls, position]
      have capacity : st.blocks.val.length < Usize.max := by
        have size := p.size
        have inside := p.inbounds
        have count := p.ctrls
        have room := limits.MAX_FUNCTION_BYTES.room
        omega
      have effect := enter_args_prefix {st with core := {st.core with pos := next}} env form decoded outer p.current.vals
        initial values base ⟨p.opened.shape.core.ordered, p.opened.shape.core.bounded⟩ capacity
      rw [rest, WP.spec_ok] at effect
      exact effect rfl
end Exec.Code
