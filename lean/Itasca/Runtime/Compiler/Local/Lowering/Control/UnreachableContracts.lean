import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty

/-! Contracts for the unreachable callback. A live callback emits the trap
before marking the compiler dead and observing the validator stack; a dead
callback only observes. The effect retains partial emission failures and the
final observation witness for metadata, coordinates, and safety consumers. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

inductive UnreachableEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      UnreachableEffect ops before state status after
  | rejected {error after} (live : before.reachable = true)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before .Unreachable = .ok (.Err error, after)) :
      UnreachableEffect ops before state (.Err error) after
  | emitted {middle status after} (live : before.reachable = true)
      (emitted : runtime.compiler.FunctionCompiler.emit ops before .Unreachable = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops {middle with reachable := false} state = .ok (status, after)) :
      UnreachableEffect ops before state status after

/-- Dead input bypasses emission entirely. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.dead
    {A : Type} (ops : runtime.platform.Alloc A) (before : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (dead : before.reachable = false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state =
      runtime.compiler.FunctionCompiler.observe ops before state := by
  simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable,
    dead, Bool.false_eq_true, ite_false]

/-- Normal returns retain their actual emission and observation evidence. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv
    {A : Type} (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state = .ok (status, after)) :
    UnreachableEffect ops before state status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨⟨reply, middle⟩, emitted, rest⟩ := bind_ok_inv _ _ _ called
    cases reply with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      exact .rejected live emitted
    | Ok unit =>
      cases unit
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      exact .emitted live emitted rest

/-- Successful returns observe a compiler whose reachability is false. -/
theorem UnreachableEffect.observation {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    (effect : UnreachableEffect ops before state (.Ok ()) after) :
    ∃ middle, middle.reachable = false ∧
      runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | dead dead observed => exact ⟨_, dead, observed⟩
  | emitted live emitted observed => exact ⟨_, rfl, observed⟩

/-- Fields permitted to change on a normal unreachable-callback return. -/
def UnreachableFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
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

theorem UnreachableEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) : UnreachableFrame before after := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    unfold UnreachableFrame
    rw [frame]
  | rejected live emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).1
    unfold UnreachableFrame
    rw [frame]
  | @emitted middle _ _ live emitted observed =>
    have emission := (runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).1
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    unfold UnreachableFrame
    rw [observation, emission]

theorem UnreachableEffect.capacity {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  cases effect with
  | dead dead observed =>
    have post := compiler_observe_inv ops law before state
    rw [observed, WP.spec_ok] at post
    exact post.2
  | rejected live emitted =>
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).1
    rw [frame]
  | @emitted middle _ _ live emitted observed =>
    have post := compiler_observe_inv ops law {middle with reachable := false} state
    rw [observed, WP.spec_ok] at post
    have frame := (runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).1
    change middle = _ at frame
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.slot_count) frame
    change middle.function.slot_count = before.function.slot_count at same
    have bound := post.2
    change middle.function.slot_count.val ≤ after.function.slot_count.val at bound
    rw [same] at bound
    exact bound

theorem UnreachableEffect.code {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {state : Itasca.code.OpIterState}
    {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : UnreachableEffect ops before state status after) (law : Platform.AllocCorrect ops) :
    after.function.code.val = before.function.code.val ∨
      after.function.code.val = before.function.code.val ++ [.Unreachable] := by
  cases effect with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state status after observed
    exact Or.inl (by rw [frame])
  | rejected live emitted =>
    exact ((runtime.compiler.FunctionCompiler.emit.inv ops before after .Unreachable _ emitted).2 law).1
  | @emitted middle _ _ live emitted observed =>
    have frame := compiler_observe_frame_raw ops {middle with reachable := false} state status after observed
    have code := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle .Unreachable (.Ok ()) emitted).2 law).1
    have same := congrArg (fun c : runtime.compiler.FunctionCompiler A => c.function.code) frame
    change after.function.code = middle.function.code at same
    rw [same]
    exact code

/-- Emission bounds suffice for normal return; no input stack layout is needed. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.total
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  split
  · step with runtime.compiler.FunctionCompiler.emit.total ops law before .Unreachable codeFits sourceFits coordinateFits
      as ⟨reply, middle, total⟩
    cases reply with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact WP.spec_mono (compiler_observe ops law {middle with reachable := false} state) (fun _ _ => True.intro)
  · exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => True.intro)

/-- Available execution consumes one instruction on live input and none on dead input. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.available
    {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat)
    (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand before state bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable ops before state ⦃ (status, after) =>
      status = .Ok () ∧ ∃ used, after.budget = {before.budget with instructions := used} ∧
        used.val = before.budget.instructions.val + (if before.reachable then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
  by_cases live : before.reachable = true
  · rw [if_pos live]
    step with runtime.compiler.FunctionCompiler.emit.available ops bound available before .Unreachable
      demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
      demand.coordinate demand.instruction as ⟨reply, middle, accepted, emitted⟩
    obtain ⟨used, code, sources, frame, usedEq, _, _⟩ := emitted
    rw [accepted]
    subst middle
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
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
