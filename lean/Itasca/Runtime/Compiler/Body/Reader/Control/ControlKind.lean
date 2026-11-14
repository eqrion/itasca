import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Body.Relations.Entry.EntrySignatures
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterSafety
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Wasm2.Visitor.Total
import Itasca.Wasm2.LoopDispatch
import Itasca.Wasm2.Trace.Acceptance
import Itasca.Wasm2.Trace.ControlRecords

/-!
Sections, each formerly its own module: RootFrame, EnterSafety, BoundaryInitial, ControlKind.
-/

/-! ## RootFrame -/

section

/-!
The root control frame retained by reader execution.

Main declarations: `reader_root_frame_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.ReachedReturnAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

private theorem paired_head_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (value : β) (found : right.head? = some value) :
    ∃ item, left.head? = some item ∧ R item value := by
  cases paired with
  | nil => simp at found
  | cons head tail =>
    simp only [List.head?_cons, Option.some.injEq] at found
    subst value
    exact ⟨_, rfl, head⟩

private theorem head_member {α : Type} {items : List α} {item}
    (found : items.head? = some item) : item ∈ items := by
  cases items with
  | nil => simp at found
  | cons first rest => simp only [List.head?_cons, Option.some.injEq] at found; subst item; simp

theorem reader_root_frame_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (compiler : runtime.compiler.FunctionCompiler A) {locals parents current}
    (physical : ScopeFrameStack locals compiler parents current)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current) :
    ∃ frame, compiler.frames.val[0]? = some frame ∧
      frame.results.val = slots (p.ft.results.val.map Translate.valueType) := by
  have bodyType := p.bodyType
  unfold Wasm2.Frames.bodyType at bodyType
  obtain ⟨saved, savedHead, savedType⟩ := Option.map_eq_some_iff.mp bodyType
  have sources := List.rel_append same.parents (.cons same.current .nil)
  obtain ⟨scope, scopeHead, matched⟩ := paired_head_right sources saved savedHead
  obtain ⟨frame, frameHead, framed⟩ := paired_head_right (List.Forall₂.flip physical.frames) scope scopeHead
  obtain ⟨C, outer, spine, header, _⟩ := p.opened
  have savedHeader : ∃ C, Wasm2.Frames.Header env C saved := by
    have member := head_member savedHead
    rcases List.mem_append.mp member with member | member
    · exact spine.headers saved member
    · have eq : saved = p.current := by simpa using member
      subst saved
      exact ⟨C, header⟩
  obtain ⟨D, savedHeader⟩ := savedHeader
  have outs := savedHeader.outputs
  rw [savedType] at outs
  have outputs : saved.outs = p.ft.results.val := by
    simpa [Wasm2.outputs, Wasm2.resolve, p.signature] using outs.symm
  refine ⟨frame, ?_, ?_⟩
  · simpa only [List.head?_eq_getElem?] using frameHead
  · rw [framed.results, matched.results, outputs]

end Itasca.Runtime.Compiler

end

/-! ## EnterSafety -/

section

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
    (expected : wasm_types.ValueType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) :
    code.pop_with_type st expected ⦃ out => out.2.ctrls = st.ctrls ∧ out.2.pos = st.pos ∧
      ∃ rest, out.2.vals.val = outer ++ rest ∧ rest <+: segment ⦄ := by
  apply WP.spec_mono (code.pop_with_type.segment st outer segment expected values base)
  rintro ⟨result, after⟩ ⟨controls, position, rest, afterValues, effect⟩
  exact ⟨controls, position, rest, afterValues, typed_pop_prefix effect⟩

@[step] theorem pop_types_prefix (st : code.OpIterState) (outer segment : List code.StackType)
    (expected : Slice wasm_types.ValueType) (values : st.vals.val = outer ++ segment)
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

@[step] theorem pop_results_prefix (st : code.OpIterState) (env : metadata.Env)
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

/-- The newly opened frame begins at an unchanged prefix of the old raw operands. -/
def EntryPrefix (before after : code.OpIterState) : Prop :=
  ∃ prior ctrl, after.ctrls.val = prior ++ [ctrl] ∧
    ctrl.value_stack_base.val ≤ after.vals.val.length ∧
    after.vals.val.take ctrl.value_stack_base.val <+: before.vals.val

@[step] theorem enter_params_prefix (st : code.BodyState) (env : metadata.Env)
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

@[step] theorem enter_args_prefix (st : code.BodyState) (env : metadata.Env)
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
    (p : Wasm2.Pending data env locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env form.kind = .ok (.Ok bt, out)) :
    EntryPrefix st.core out.core := by
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
    (p : Wasm2.Pending data env locals index st) (initial : form.Initial)
    (accepted : code.enter_info st data env form.kind = .ok (.Ok bt, out)) :
    ∃ ins outs, resolve env (inputs bt) = some ins ∧ resolve env (outputs bt) = some outs := by
  have erased : code.enter st data env form.kind = .ok (.Ok (), out) := by
    simp [code.enter, accepted, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C, outer, spine, header, parentBase, typed, ctrls, blocks, vals⟩ := p.opened
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have effect := code.enter.sound st data env form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, parentBase]) p.opened.shape.core capacity
  rw [erased, WP.spec_ok] at effect
  obtain ⟨sourceBt, ins, outs, decoded, inputs, outputs, _⟩ := effect rfl
  have info := code.enter_info.bytes st data env form.kind p.opened.shape.core capacity
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
    {data env locals index st} (p : Wasm2.Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (signatures : SignatureSequence compiler.signatures.val env.types.val)
    (observed : ObservedStack compiler st.core.vals.val)
    (coordinate : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max)
    (pcBound : compiler.function.code.val.length+1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    CallbackTrace.bodyRun (code.enter_info st data env form.kind)
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) (enterAction form) compiler ⦃ out =>
        out.1 = .Ok () → ObservedStack out.2.2 out.2.1.core.vals.val ⦄ := by
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply reader_body_run_reached _ _ _ compiler (fun s c => ObservedStack c s.core.vals.val)
  · exact WP.spec_mono (code.enter_info.total st data env form.kind p.opened.shape.core capacity) (by simp)
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

end

/-! ## BoundaryInitial -/

section

/-!
The initial reader boundary before body compilation.

Main declarations: `ReaderBoundaryWasm2.initial`. A direct consumer is `Compiler.Body.Reader.Replay.IndexedCompilerInitial`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundaryWasm2.initial (data : Slice U8) (env : metadata.Env)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (ft : wasm_types.FuncType)
    (signature : env.types.val[index.val]? = some ft)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ReaderBoundaryWasm2 data env locals index ft (Wasm2.initial index) []
      (Wasm2.Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) := by
  refine ⟨signature, ?_, ?_, rfl, ?_, ?_⟩
  · constructor <;> simp [Wasm2.initial, size]
  · apply Wasm2.Frames.Open.start env _ (EnvTranslation.context_wf env ⟨locals, ft.results⟩)
    · simp [Wasm2.resolve, Wasm2.inputs, signature]
    · simp [Wasm2.resolve, Wasm2.outputs, signature]
    · rfl
    · rfl
    · rfl
  · simpa [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh,
      Wasm2.Frames.Form.opening, Wasm2.initial] using Wasm2.Consumed.nil (data := data) 0#usize (by simp)
  · simp [Wasm2.Frames.trace, Wasm2.Frames.Saved.trace, Wasm2.Frames.Saved.fresh, Wasm2.Frames.Form.opening]
end Itasca.Runtime.Compiler

end

/-! ## ControlKind -/

section

/-!
Checked metadata-producing profile readers, excluding the streamed table reader, which has a separate source-count replay proof.

Main declarations: `ControlReaderKind` and `opcode`. A direct consumer is `Compiler.Body.Reader.Control.ControlCheckedPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Checked metadata-producing profile readers, excluding the streamed table
reader, which has a separate source-count replay proof. -/
inductive ControlReaderKind where
  | block
  | loop
  | if_
  | else_
  | end_
  | br
  | br_if
  | return_
  | call
  | call_indirect

namespace ControlReaderKind

def opcode : ControlReaderKind → U8
  | .block => 2#u8
  | .loop => 3#u8
  | .if_ => 4#u8
  | .else_ => 5#u8
  | .end_ => 11#u8
  | .br => 12#u8
  | .br_if => 13#u8
  | .return_ => 15#u8
  | .call => 16#u8
  | .call_indirect => 17#u8

/-- Every control opcode belongs to the shared reader inventory. -/
theorem of_opcode_mem (opcode : U8)
    (member : opcode.val ∈ [2,3,4,5,11,12,13,15,16,17]) : ∃ kind : ControlReaderKind, opcode = kind.opcode := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal | equal | equal | equal | equal
  · exact ⟨.block,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.loop,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.if_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.else_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.end_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.br_if,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.return_,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call,UScalar.eq_of_val_eq equal⟩
  · exact ⟨.call_indirect,UScalar.eq_of_val_eq equal⟩

def Parameter : ControlReaderKind → Type
  | .block => signature.BlockType
  | .loop => signature.BlockType
  | .if_ => signature.BlockType
  | .else_ => code.LabelKind × signature.BlockType
  | .end_ => code.LabelKind × signature.BlockType
  | .br => U32 × signature.ResultType
  | .br_if => U32 × signature.ResultType
  | .return_ => Unit
  | .call => U32
  | .call_indirect => U32 × U32

def read (kind : ControlReaderKind) (st : code.BodyState) (data : Slice U8)
    (env : metadata.Env) (index : U32) : Result (core.result.Result kind.Parameter error.OpError × code.BodyState) :=
  match kind with
  | .block => code.enter_info st data env .Block
  | .loop => code.enter_info st data env .Loop
  | .if_ => code.enter_info st data env .Then
  | .else_ => code.end_frame_info st env true
  | .end_ => code.end_frame_info st env false
  | .br => code.branch_info st data env false
  | .br_if => code.branch_info st data env true
  | .return_ => Wasm2.returnStep st env index
  | .call => code.call_info st data env
  | .call_indirect => code.call_indirect_info st data env

def action : (kind : ControlReaderKind) → kind.Parameter → Action
  | .block => .block
  | .loop => .loop
  | .if_ => .if_
  | .else_ => fun arg => .else_ arg.2
  | .end_ => fun arg => .end_ arg.1 arg.2
  | .br => fun arg => .br arg.1 arg.2
  | .br_if => fun arg => .br_if arg.1 arg.2
  | .return_ => fun _ => .return_
  | .call => .call
  | .call_indirect => fun arg => .call_indirect arg.1 arg.2

/-- Every inventory entry agrees with actual complete-profile dispatch. -/
theorem dispatch {V : Type} (kind : ControlReaderKind) (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (before : V) :
    code.step_profile visitor st data env ctx index kind.opcode before =
      Wasm2.CallbackTrace.bodyRun (kind.read st data env index) visitor kind.action before := by
  cases kind
  · exact Wasm2.CallbackTrace.dispatch_block visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_loop visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_if visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_else visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_end visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_br visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_br_if visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_return visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_call visitor st data env ctx index before
  · exact Wasm2.CallbackTrace.dispatch_call_indirect visitor st data env ctx index before

/-- Source byte provenance for every metadata-producing reader in this
inventory. This also bounds its accepted final cursor by input length. -/
theorem records {data env locals index st} (kind : ControlReaderKind)
    (pending : Wasm2.Pending data env locals index st) {V : Type}
    (visitor : code.OpVisitor V) (observe : V → List Observation)
    (recorded : Records visitor observe) (ctx : code.Context)
    (byte : data.val[pending.start.val]'pending.inbounds = kind.opcode) :
    Wasm2.CallbackTrace.ProfileStepRecords pending visitor observe ctx kind.opcode := by
  cases kind
  · exact Wasm2.CallbackTrace.step_block pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_loop pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_if pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_else pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_end pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_br pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_br_if pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_return pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_call pending visitor observe recorded ctx byte
  · exact Wasm2.CallbackTrace.step_call_indirect pending visitor observe recorded ctx byte

end ControlReaderKind
end Itasca.Runtime.Compiler

end
