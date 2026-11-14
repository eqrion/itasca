import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

/-! Canonical return-callback contracts retain the selected root frame, checked
result source, emission and final observation, including partial failures. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

inductive ReturnEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      ReturnEffect ops before state status after
  | underflow {frame} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (source : lift (U32.checked_sub before.height frame.results) = .ok none) :
      ReturnEffect ops before state (.Err .OutOfMemory) before
  | rejected {frame source error after} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (position : lift (U32.checked_sub before.height frame.results) = .ok (some source))
      (emitted : runtime.compiler.FunctionCompiler.emit ops before (.Return source frame.results) = .ok (.Err error, after)) :
      ReturnEffect ops before state (.Err error) after
  | emitted {frame source middle status after} (live : before.reachable = true)
      (selected : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) before.frames 0#usize = .ok frame)
      (position : lift (U32.checked_sub before.height frame.results) = .ok (some source))
      (emitted : runtime.compiler.FunctionCompiler.emit ops before (.Return source frame.results) = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops {middle with reachable := false} state = .ok (status, after)) :
      ReturnEffect ops before state status after

/-- Dead input bypasses emission entirely. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.dead
    {A : Type} (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return,
    dead, Bool.false_eq_true, ite_false]

/-- Normal returns retain their actual emission and observation evidence. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv
    {A : Type} (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state = .ok (status, after)) :
    ReturnEffect ops before state status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨frame, selected, rest⟩ := bind_ok_inv _ _ _ called
    obtain ⟨source, position, rest⟩ := bind_ok_inv _ _ _ rest
    cases source with
    | none =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .underflow live selected position
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨reply, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ rest
      cases reply with
      | Err error =>
        simp only [uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        exact .rejected live selected position emitted
      | Ok value =>
        cases value
        simp only [uncurry_apply_pair, bind_ok] at rest
        exact .emitted live selected position emitted rest

/-- Successful returns observe a compiler whose reachability is false. -/
theorem ReturnEffect.observation {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    (effect : ReturnEffect ops before state (.Ok ()) after) :
    ∃ middle, middle.reachable = false ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | dead dead observed => exact ⟨_, dead, observed⟩
  | emitted live selected position emitted observed => exact ⟨_, rfl, observed⟩

/-- Fields permitted to change on a normal return-callback return. -/
def ReturnFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget
    before := after.before
    height := after.height
    next_source := after.next_source
    reachable := after.reachable
    function := {before.function with
      code := after.function.code
      source_offsets := after.function.source_offsets
      max_stack := after.function.max_stack
      slot_count := after.function.slot_count}}

theorem ReturnEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ReturnEffect ops before state status after) : ReturnFrame before after := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    unfold ReturnFrame
    rw [frame]
  | underflow live selected position => rfl
  | rejected live selected position emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after _ _ emitted).1
    unfold ReturnFrame
    rw [frame]
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have emission := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).1
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    unfold ReturnFrame
    rw [observation, emission]

theorem ReturnEffect.capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : ReturnEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  cases effect with
  | dead dead observed =>
    have post := compiler_observe_inv ops law before state
    rw [observed, WP.spec_ok] at post
    exact post.2
  | underflow live selected position => exact Nat.le_refl _
  | rejected live selected position emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after _ _ emitted).1
    rw [frame]
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have post := compiler_observe_inv ops law {middle with reachable := false} state
    rw [observed, WP.spec_ok] at post
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).1
    change middle = _ at frame
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.slot_count) frame
    change middle.function.slot_count = before.function.slot_count at same
    have bound := post.2
    change middle.function.slot_count.val ≤ after.function.slot_count.val at bound
    rw [same] at bound
    exact bound

/-- A live return needs a root frame; checked source underflow is a normal error. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.total
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (root : before.reachable = true → 0 < before.frames.val.length)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : before.reachable = true
  · rw [if_pos live]
    have framesBound := root live
    step as ⟨frame, selected⟩
    step as ⟨source, position⟩
    cases source with
    | none => simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.FunctionCompiler.emit.total ops law before (.Return source frame.results) codeFits sourceFits coordinateFits
        as ⟨reply, middle⟩
      cases reply with
      | Err error =>
        simp only [bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      | Ok value =>
        cases value
        simp only [bind_ok]
        exact WP.spec_mono (compiler_observe ops law {middle with reachable := false} state) (fun _ _ => True.intro)
  · rw [if_neg live]
    exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => True.intro)

/-- Successful return charges one instruction on live input and none on dead input. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.available
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat)
    (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand before state bound) (body : runtime.compiler.Frame)
    (bodyFrame : before.reachable = true → before.frames.val[0]? = some body)
    (height : before.reachable = true → body.results.val ≤ before.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops before state ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (if before.reachable then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : before.reachable = true
  · rw [if_pos live]
    have framesBound : 0 < before.frames.length := (List.getElem?_eq_some_iff.mp (bodyFrame live)).1
    step as ⟨frame, selected⟩
    have same : frame = body := selected.trans (List.getElem?_eq_some_iff.mp (bodyFrame live)).2
    rw [same]
    have resultFits := height live
    step as ⟨source, position⟩
    cases source with
    | none => simp only at position; omega
    | some source =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with runtime.compiler.FunctionCompiler.emit.available ops bound available before (.Return source body.results)
        demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
        demand.coordinate demand.instruction as ⟨reply, middle, accepted, emitted⟩
      obtain ⟨used, code, sources, frame, usedEq, _, _⟩ := emitted
      rw [accepted]
      subst middle
      simp only [bind_ok]
      apply WP.spec_mono (compiler_observe_available_budget ops bound available
        {before with
          reachable := false
          budget := {before.budget with instructions := used}
          function := {before.function with code, source_offsets := sources}}
        state demand.operands demand.slots)
      intro output post
      exact ⟨post.1, used, post.2, by simpa only [live, ite_true] using usedEq⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available before state demand.operands demand.slots)
    intro output post
    exact ⟨post.1, before.budget.instructions, by simpa only using post.2, by simp only [if_neg live, Nat.add_zero]⟩

end Itasca.Runtime.Compiler
