import Itasca.Runtime.Compiler.Local.Lowering.Control.BranchContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-! Canonical contracts for direct and conditional branch callbacks. The live
branch call and final observation retain their exact intermediate states; dormant
callbacks do not inspect their branch target. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

def branchCallbackSkip (conditional : Bool) : U32 := if conditional then 1#u32 else 0#u32

def branchCallbackObserved {A : Type} (conditional : Bool)
    (compiler : runtime.compiler.FunctionCompiler A) : runtime.compiler.FunctionCompiler A :=
  if conditional then compiler else {compiler with reachable := false}

/-- A live branch can reject after partial progress. Only successful unconditional
branches mark the continuation unreachable before observing its source stack. -/
inductive BranchCallbackEffect {A : Type} (ops : runtime.platform.Alloc A) (state : Itasca.code.OpIterState)
    (before : runtime.compiler.FunctionCompiler A) (depth : U32) (conditional : Bool) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | dead {status after} (dead : before.reachable = false)
      (observed : runtime.compiler.FunctionCompiler.observe ops before state = .ok (status, after)) :
      BranchCallbackEffect ops state before depth conditional status after
  | rejected {error after} (live : before.reachable = true)
      (branched : runtime.compiler.control.FunctionCompiler.branch ops before depth (branchCallbackSkip conditional) conditional = .ok (.Err error, after)) :
      BranchCallbackEffect ops state before depth conditional (.Err error) after
  | branched {middle status after} (live : before.reachable = true)
      (branch : runtime.compiler.control.FunctionCompiler.branch ops before depth (branchCallbackSkip conditional) conditional = .ok (.Ok (), middle))
      (observed : runtime.compiler.FunctionCompiler.observe ops (branchCallbackObserved conditional middle) state = .ok (status, after)) :
      BranchCallbackEffect ops state before depth conditional status after

/-- The branch's existing normality conditions apply only to live callbacks. -/
def BranchCallbackNormal {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (depth : U32) (conditional : Bool) : Prop :=
  ∃ selected : BranchSelection before depth, ∀ source : U32,
    source.val + (branchWidth selected.frame).val + (branchCallbackSkip conditional).val = before.height.val →
    (conditional = true ∧ before.before.val = []) ∨
      (Platform.AllocCorrect ops ∧ BranchTotalBounds before selected.frame (branchInstructionCount conditional selected.frame source))

/-- Live availability retains the exact operand interval and branch demand. -/
def BranchCallbackReady {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (depth : U32) (conditional : Bool) (bound : Nat) : Prop :=
  ∃ selected : BranchSelection before depth, ∃ source : U32,
    source.val + (branchWidth selected.frame).val + (branchCallbackSkip conditional).val = before.height.val ∧
    (conditional = true → ∃ condition, runtime.compiler.FunctionCompiler.operand ops before 1#usize = .ok (.Ok condition)) ∧
    BranchDemand before selected.frame bound (branchInstructionCount conditional selected.frame source)

/-- A dormant callback retains its budget. A live one charges exactly the
instruction sequence selected by the branch, including an elided copy. -/
def BranchCallbackBudget {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (depth : U32) (conditional : Bool) : Prop :=
  if before.reachable then ∃ selected : BranchSelection before depth, ∃ source : U32,
    source.val + (branchWidth selected.frame).val + (branchCallbackSkip conditional).val = before.height.val ∧
    BranchBudget before after (branchInstructionCount conditional selected.frame source)
  else after.budget = before.budget

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (status, after)) :
    BranchCallbackEffect ops state before depth false status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨⟨answer, branched⟩, branchCall, tail⟩ := bind_ok_inv _ _ _ called
    cases answer with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact .rejected live branchCall
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      exact .branched live branchCall tail

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (ready : before.reachable = true → BranchCallbackNormal ops before depth false) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  cases live : before.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => trivial)
  | true =>
    simp only [ite_true]
    obtain ⟨selected, normal⟩ := ready live
    step with runtime.compiler.control.FunctionCompiler.branch.total ops before depth 0#u32 false selected normal
      as ⟨status, branched, post⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact WP.spec_mono (compiler_observe ops law {branched with reachable := false} state) (fun _ _ => trivial)

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (ready : before.reachable = true → BranchCallbackReady ops before depth false bound)
    (request : state.vals.length ≤ bound)
    (slotsFit : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types ⦃ (status, after) =>
      status = .Ok () ∧ BranchCallbackBudget before after depth false ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  cases live : before.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available before state request slotsFit)
    rintro ⟨status, after⟩ post
    simpa only [uncurry_apply_pair, BranchCallbackBudget, live, Bool.false_eq_true, ite_false] using post
  | true =>
    simp only [ite_true]
    obtain ⟨selected, source, position, condition, demand⟩ := ready live
    obtain ⟨⟨status, branched⟩, branchCall, accepted, budget⟩ := WP.spec_imp_exists
      (runtime.compiler.control.FunctionCompiler.branch.available ops bound available before depth 0#u32 false
        selected source position condition demand)
    subst status
    rw [branchCall]
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before branched depth 0#u32 false (.Ok ()) branchCall).frame
    have slots : ({branched with reachable := false}).function.local_slots = before.function.local_slots := by rw [frame]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available {branched with reachable := false} state request
      (by rw [slots]; exact slotsFit))
    rintro ⟨status, after⟩ ⟨accepted, kept⟩
    refine ⟨accepted, ?_⟩
    simp only [BranchCallbackBudget, live, ite_true]
    refine ⟨selected, source, position, ?_⟩
    obtain ⟨used, budgetEq, usedEq⟩ := budget
    exact ⟨used, kept.trans budgetEq, usedEq⟩

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (status, after)) :
    BranchCallbackEffect ops state before depth true status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at called
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at called
    exact .dead live called
  | true =>
    simp only [live, ite_true] at called
    obtain ⟨⟨answer, branched⟩, branchCall, tail⟩ := bind_ok_inv _ _ _ called
    cases answer with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl⟩ := tail
      exact .rejected live branchCall
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      exact .branched live branchCall tail

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (ready : before.reachable = true → BranchCallbackNormal ops before depth true) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  cases live : before.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact WP.spec_mono (compiler_observe ops law before state) (fun _ _ => trivial)
  | true =>
    simp only [ite_true]
    obtain ⟨selected, normal⟩ := ready live
    step with runtime.compiler.control.FunctionCompiler.branch.total ops before depth 1#u32 true selected normal
      as ⟨status, branched, post⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact WP.spec_mono (compiler_observe ops law branched state) (fun _ _ => trivial)

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (ready : before.reachable = true → BranchCallbackReady ops before depth true bound)
    (request : state.vals.length ≤ bound)
    (slotsFit : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types ⦃ (status, after) =>
      status = .Ok () ∧ BranchCallbackBudget before after depth true ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
  cases live : before.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available before state request slotsFit)
    rintro ⟨status, after⟩ post
    simpa only [uncurry_apply_pair, BranchCallbackBudget, live, Bool.false_eq_true, ite_false] using post
  | true =>
    simp only [ite_true]
    obtain ⟨selected, source, position, condition, demand⟩ := ready live
    obtain ⟨⟨status, branched⟩, branchCall, accepted, budget⟩ := WP.spec_imp_exists
      (runtime.compiler.control.FunctionCompiler.branch.available ops bound available before depth 1#u32 true
        selected source position condition demand)
    subst status
    rw [branchCall]
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have frame := (runtime.compiler.control.FunctionCompiler.branch.inv ops before branched depth 1#u32 true (.Ok ()) branchCall).frame
    have slots : (branched).function.local_slots = before.function.local_slots := by rw [frame]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available branched state request
      (by rw [slots]; exact slotsFit))
    rintro ⟨status, after⟩ ⟨accepted, kept⟩
    refine ⟨accepted, ?_⟩
    simp only [BranchCallbackBudget, live, ite_true]
    refine ⟨selected, source, position, ?_⟩
    obtain ⟨used, budgetEq, usedEq⟩ := budget
    exact ⟨used, kept.trans budgetEq, usedEq⟩


/-- Only branch-owned buffers, frames and observation state can change. -/
def BranchCallbackFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with budget := after.budget, frames := after.frames, reachable := after.reachable, before := after.before, height := after.height, next_source := after.next_source, function := {before.function with code := after.function.code, source_offsets := after.function.source_offsets, max_stack := after.function.max_stack, slot_count := after.function.slot_count}}

theorem BranchCallbackEffect.frame {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {conditional : Bool} {status}
    (effect : BranchCallbackEffect ops state before depth conditional status after) : BranchCallbackFrame before after := by
  unfold BranchCallbackFrame
  cases effect with
  | dead dead observed => rw [compiler_observe_frame_raw ops _ _ _ _ observed]
  | rejected live branched =>
    have unchanged := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branched).frame
    rw [unchanged]
  | branched live branch observed =>
    have unchanged := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branch).frame
    rw [compiler_observe_frame_raw ops _ _ _ _ observed, unchanged]
    cases conditional <;> rfl

theorem BranchCallbackEffect.observation {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {conditional : Bool}
    (effect : BranchCallbackEffect ops state before depth conditional (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | dead dead observed => exact ⟨_, observed⟩
  | branched live branch observed => exact ⟨_, observed⟩

theorem BranchCallbackEffect.observation_slots {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {conditional : Bool}
    (effect : BranchCallbackEffect ops state before depth conditional (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) ∧
      middle.function.slot_count = before.function.slot_count ∧ middle.function.local_slots = before.function.local_slots := by
  cases effect with
  | dead dead observed => exact ⟨_, observed, rfl, rfl⟩
  | branched live branch observed =>
    have unchanged := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branch).frame
    refine ⟨_, observed, ?_, ?_⟩ <;> rw [unchanged] <;> cases conditional <;> rfl

theorem BranchCallbackEffect.capacity {A : Type} {ops : runtime.platform.Alloc A} {state : Itasca.code.OpIterState}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32} {conditional : Bool} {status}
    (effect : BranchCallbackEffect ops state before depth conditional status after) (law : Platform.AllocCorrect ops) :
    before.function.slot_count.val ≤ after.function.slot_count.val := by
  have observedSlots {compiler changed : runtime.compiler.FunctionCompiler A} {answer}
      (called : runtime.compiler.FunctionCompiler.observe ops compiler state = .ok (answer, changed)) :
      compiler.function.slot_count.val ≤ changed.function.slot_count.val := by
    have post := compiler_observe_inv ops law compiler state
    rw [called, WP.spec_ok] at post
    exact post.2
  cases effect with
  | dead dead observed => exact observedSlots observed
  | rejected live branched =>
    have unchanged := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branched).frame
    rw [unchanged]
  | branched live branch observed =>
    have unchanged := (runtime.compiler.control.FunctionCompiler.branch.inv ops _ _ _ _ _ _ branch).frame
    have slots := observedSlots observed
    rw [unchanged] at slots
    cases conditional <;> exact slots

/-- Exact branch charges imply the familiar two/three instruction upper bounds. -/
theorem BranchCallbackBudget.bounds {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {depth : U32} {conditional : Bool} (effect : BranchCallbackBudget before after depth conditional) :
    ∃ used, after.budget = {before.budget with instructions := used} ∧
      before.budget.instructions.val ≤ used.val ∧ used.val ≤ before.budget.instructions.val + (if conditional then 3 else 2) := by
  unfold BranchCallbackBudget at effect
  cases live : before.reachable with
  | false =>
    simp only [live, Bool.false_eq_true, ite_false] at effect
    refine ⟨before.budget.instructions, ?_, Nat.le_refl _, ?_⟩
    · exact effect
    · omega
  | true =>
    simp only [live, ite_true] at effect
    obtain ⟨selected, source, position, used, budgetEq, count⟩ := effect
    have bound : branchInstructionCount conditional selected.frame source ≤ (if conditional then 3 else 2) := by
      unfold branchInstructionCount
      split <;> cases conditional <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
    exact ⟨used, budgetEq, by omega, by omega⟩

end Itasca.Runtime.Compiler
