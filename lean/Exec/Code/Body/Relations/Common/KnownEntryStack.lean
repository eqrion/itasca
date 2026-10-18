import Exec.Code.Local.Relations.Common.KnownPopStack
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.Wasm2 Itasca.ResultFacts

/-- Entry only pops existing operands and appends concrete signature types,
even when the current validator segment is polymorphic. -/
@[step] theorem enter_params_known (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (shape : Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max)
    (known : ConcreteStack st.core.vals.val) :
    enterParams st env form.kind bt ⦃ out => out.1 = .Ok () → ConcreteStack out.2.core.vals.val ⦄ := by
  have both := concreteStack_append.mp (values ▸ known)
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with pop_results_concrete st.core env (inputs bt) outer segment values base both.2
    as ⟨result, middle, controls, position, rest, middleValues, restKnown⟩
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
    rw [appended, frameValues, middleValues]
    exact concreteStack_append.mpr ⟨concreteStack_append.mpr ⟨both.1, restKnown⟩, concrete_values types⟩
  · step*

@[step] theorem enter_args_known (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (outer segment : List code.StackType)
    (initial : form.Initial)
    (values : st.core.vals.val = outer ++ segment) (base : (Control.base st.core).val = outer.length)
    (shape : Control.Shape st.core) (capacity : st.blocks.val.length < Usize.max)
    (known : ConcreteStack st.core.vals.val) :
    enterArgs st env form.kind bt ⦃ out => out.1 = .Ok () → ConcreteStack out.2.core.vals.val ⦄ := by
  rcases initial with rfl | rfl | rfl
  · exact enter_params_known st env .block bt outer segment values base shape capacity known
  · exact enter_params_known st env .loop bt outer segment values base shape capacity known
  · have both := concreteStack_append.mp (values ▸ known)
    simp only [enterArgs, Frames.Form.kind]
    step with pop_with_type_concrete st.core outer segment .I32 values base both.2
      as ⟨result, middle, controls, position, rest, middleValues, restKnown⟩
    step
    split
    · have middleShape := shape.replace_operands controls (by simp [base, middleValues])
      exact enter_params_known {st with core := middle} env .then_ bt outer rest middleValues
        (by simpa [Control.base, controls] using base) middleShape (by simpa [controls] using capacity)
        (middleValues ▸ concreteStack_append.mpr ⟨both.1, restKnown⟩)
    · step*

/-- Successful canonical entry preserves concrete physical operands without
assuming that the discarded current segment is reachable. -/
theorem reader_enter_known_wasm2 {data env locals index st out bt} {form : Frames.Form}
    (p : Wasm2.Pending data env locals index st) (initial : form.Initial)
    (known : ConcreteStack st.core.vals.val)
    (accepted : code.enter_info st data env form.kind = .ok (.Ok bt, out)) :
    ConcreteStack out.core.vals.val := by
  have erased : code.enter st data env form.kind = .ok (.Ok (), out) := by
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
      have effect := enter_args_known {st with core := {st.core with pos := next}} env form decoded outer p.current.vals
        initial values base ⟨p.opened.shape.core.ordered, p.opened.shape.core.bounded⟩ capacity known
      rw [rest, WP.spec_ok] at effect
      exact effect rfl

end Exec.Code
