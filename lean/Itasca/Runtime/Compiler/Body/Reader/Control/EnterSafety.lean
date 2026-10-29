import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntrySignatures
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterSafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.BodySafety
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Wasm2.Visitor.Total

/-!
Typed-pop prefixes and safe control-scope entry. EntryPrefix carries the parameter/argument bounds consumed by the entering reader callback.
-/

/-! ## Reader Pop Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem popped_prefix {poly before value after}
    (popped : StackSemantics.Popped poly before value after) : after <+: before := by
  cases popped with
  | explicit => exact ⟨_, rfl⟩
  | implicit => exact ⟨[], by simp⟩

theorem typed_pop_prefix {poly before expected result after}
    (effect : StackSemantics.TypedPopResult poly before expected result after) : after <+: before := by
  cases result with
  | Ok value => exact popped_prefix effect.1
  | Err error =>
    rcases effect with ⟨_, _, _, rfl⟩ | ⟨_, value, popped, _⟩
    · exact List.nil_prefix
    · exact popped_prefix popped

@[step] theorem pop_with_type_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, typed_pop_prefix effect⟩

@[step] theorem pop_types_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) :
    code.pop_types st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  unfold code.pop_types code.pop_types_loop
  apply loop.spec_decr_nat (fun p => p.2.val)
    (fun p => p.2.val ≤ expected.val.length ∧ p.1.ctrls = st.ctrls ∧ p.1.pos = st.pos ∧
      ∃ rest, p.1.vals.val = outer ++ rest ∧ rest <+: segment)
  · rintro ⟨current, index⟩ ⟨bound, controls, position, currentSegment, currentValues, currentPrefix⟩
    dsimp only at bound controls position currentValues currentPrefix
    unfold code.pop_types_loop.body
    dsimp only
    split
    · simp only [WP.spec_ok]
      exact ⟨controls, position, currentSegment, currentValues, currentPrefix⟩
    · step as ⟨next, decrement⟩
      have inBounds : next.val < expected.val.length := by scalar_tac
      step as ⟨ty, tyEq⟩
      have currentBase : (Control.base current).val = outer.length := by
        simpa only [Control.base, controls] using base
      step with pop_with_type_prefix current outer currentSegment ty currentValues currentBase
        as ⟨result, after, afterControls, afterPosition, rest, afterValues, afterPrefix⟩
      cases result with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
        exact ⟨afterControls.trans controls, afterPosition.trans position, rest, afterValues,
          afterPrefix.trans currentPrefix⟩
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
        exact ⟨by scalar_tac, afterControls.trans controls, afterPosition.trans position,
          ⟨rest, afterValues, afterPrefix.trans currentPrefix⟩, by scalar_tac⟩
  · exact ⟨by simp, rfl, rfl, segment, values, ⟨[], by simp⟩⟩

@[step] theorem pop_results_prefix (st : code.OpIterState) (env : module.Env)
    (view : signature.ResultType) (outer segment : List code.StackType)
    (values : st.vals.val = outer ++ segment) (base : (Control.base st).val = outer.length) :
    code.pop_results st env view ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  cases view with
  | Empty =>
    simp only [code.pop_results, WP.spec_ok]
    exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
  | One ty =>
    unfold code.pop_results
    step with pop_with_type_prefix st outer segment ty values base
      as ⟨result, after, controls, position, rest, afterValues, afterPrefix⟩
    cases result <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | «Type» index part =>
    unfold code.pop_results
    step as ⟨i, castEq⟩
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, trivial, segment, values, ⟨[], by simp⟩⟩
    · cases part <;> step as ⟨ty, tyEq⟩
      all_goals exact pop_types_prefix st outer segment _ values base
end Itasca.Runtime.Compiler

end

/-! ## Reader Enter Prefix -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler
namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end

/-! ## Reader Enter Safety -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2

theorem reader_enter_signature_wasm2 {data env locals index st out bt} {form : Frames.Form}
    (p : Wasm2.Pending data env .Wasm2 locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env .Wasm2 form.kind = .ok (.Ok bt, out)) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs := by
  have erased : code.enter st data env .Wasm2 form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, parentBase, typed, ctrls, blocks, vals⟩ := p.opened
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have effect := code.enter.sound st data env .Wasm2 form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, parentBase]) p.opened.shape.core capacity
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, decoded, _, inputs, outputs, _⟩ := effect rfl
  have info := code.enter_info.bytes st data env .Wasm2 form.kind p.opened.shape.core capacity
  rw [accepted, WP.spec_ok] at info
  obtain ⟨rfl, _⟩ := (info bt rfl).unique decoded
  exact ⟨ins,outs,inputs,outputs⟩

theorem EntryPrefix.height_bound {A} {compiler : runtime.compiler.FunctionCompiler A}
    {before after : code.OpIterState}
    (kept : EntryPrefix before after) (observed : ObservedStack compiler before.vals.val) :
    ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
      ctrl.value_stack_base.val ≤ after.vals.val.length ∧
      compiler.function.local_slots.val + stackWords (after.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
  obtain ⟨prior,ctrl,controls,bound,suffix,eq⟩ := kept
  refine ⟨prior,ctrl,controls,bound,?_⟩
  have limited := observed.prefix_bound (after.vals.val.take ctrl.value_stack_base.val).length
  rw [← eq,List.take_left] at limited
  exact limited

theorem compiler_enter_reader_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    {data env locals index st} (p : Wasm2.Pending data env .Wasm2 locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CallbackTrace.bodyRun (code.enter_info st data env .Wasm2 form.kind)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.enter_info.total st data env .Wasm2 form.kind p.opened.shape.core capacity) (by simp)
  · intro out bt read
    obtain ⟨ins,outs,inputs,outputs⟩ := reader_enter_signature_wasm2 p initial read
    obtain ⟨signature,selected,_⟩ := signatures.select inputs outputs
    obtain ⟨prior,ctrl,controls,bound,height⟩ :=
      (reader_enter_prefix_wasm2 p initial read).height_bound observed
    have normal := compiler_enter_total ops law compiler out.core ctrl prior form.kind bt signature
      controls selected bound height coordinate pcBound codeFits sourceFits mapsFit framesFit
      (by rcases initial with rfl | rfl | rfl <;> simp [Frames.Form.kind])
    rcases initial with rfl | rfl | rfl <;> exact normal
end Itasca.Runtime.Compiler

end
