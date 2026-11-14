import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Frame

/-! Canonical contracts for collecting and consuming branch-table labels.
The contracts retain charge, append, lowering and observation states, including
partial progress before an ordinary error. -/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Label collection records the actual charge and optional vector append. -/
inductive TableLabelEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (depth : U32) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | rejected {error budget}
      (charged : runtime.compiler.Budget.charge ops before.budget .BranchTableEntries = .ok (.Err error, budget)) :
      TableLabelEffect ops before depth (.Err error) {before with budget}
  | pushed {chargedBudget status budget depths}
      (charged : runtime.compiler.Budget.charge ops before.budget .BranchTableEntries = .ok (.Ok (), chargedBudget))
      (pushed : runtime.compiler.Budget.push ops chargedBudget before.table_depths depth = .ok (status, budget, depths)) :
      TableLabelEffect ops before depth status {before with budget, table_depths := depths}

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state depth = .ok (status, after)) :
    TableLabelEffect ops before depth status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label at called
  obtain ⟨⟨answer, budget⟩, charged, tail⟩ := bind_ok_inv _ _ _ called
  cases answer with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl⟩ := tail
    exact .rejected charged
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨answer, finalBudget, depths⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl⟩ := tail
    exact .pushed charged pushed

/-- Both accepted and rejected label collection retain all non-scratch state. -/
theorem TableLabelEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth status}
    (effect : TableLabelEffect ops before depth status after) :
    after = {before with budget := after.budget, table_depths := after.table_depths} := by
  cases effect <;> rfl

theorem TableLabelEffect.appended {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.FunctionCompiler A} {depth}
    (effect : TableLabelEffect ops before depth (.Ok ()) after) (law : Platform.AllocCorrect ops) :
    after.table_depths.val = before.table_depths.val ++ [depth] := by
  cases effect with
  | pushed charged pushed => exact (budget_push_success ops law _ _ _ _ _ pushed).2

/-- The final callback may reject while collecting the default or lowering the
live dispatch. Successful lowering clears scratch before observing the stack. -/
inductive TableCallbackEffect {A : Type} (ops : runtime.platform.Alloc A)
    (state : Itasca.code.OpIterState) (before : runtime.compiler.FunctionCompiler A) (fallback : U32) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.FunctionCompiler A → Prop where
  | labelRejected {error after}
      (labeled : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Err error, after)) :
      TableCallbackEffect ops state before fallback (.Err error) after
  | lowerRejected {labeled error after}
      (labelCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled))
      (live : labeled.reachable = true)
      (lowered : runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Err error, after)) :
      TableCallbackEffect ops state before fallback (.Err error) after
  | live {labeled lowered cleared status after}
      (labelCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled))
      (live : labeled.reachable = true)
      (lowerCall : runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled = .ok (.Ok (), lowered))
      (clearCall : runtime.clear lowered.table_depths = .ok cleared)
      (observed : runtime.compiler.FunctionCompiler.observe ops {lowered with reachable := false, table_depths := cleared} state = .ok (status, after)) :
      TableCallbackEffect ops state before fallback status after
  | dead {labeled cleared status after}
      (labelCall : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled))
      (dead : labeled.reachable = false)
      (clearCall : runtime.clear labeled.table_depths = .ok cleared)
      (observed : runtime.compiler.FunctionCompiler.observe ops {labeled with table_depths := cleared} state = .ok (status, after)) :
      TableCallbackEffect ops state before fallback status after

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops before state fallback types = .ok (status, after)) :
    TableCallbackEffect ops state before fallback status after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at called
  obtain ⟨⟨answer, labeled⟩, labelCall, tail⟩ := bind_ok_inv _ _ _ called
  cases answer with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl⟩ := tail
    exact .labelRejected labelCall
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    cases live : labeled.reachable with
    | false =>
      simp only [live, Bool.false_eq_true, ite_false] at tail
      obtain ⟨cleared, clearCall, observed⟩ := bind_ok_inv _ _ _ tail
      exact .dead labelCall live clearCall (by simpa only [live] using observed)
    | true =>
      simp only [live, ite_true] at tail
      obtain ⟨⟨answer, lowered⟩, lowerCall, tail⟩ := bind_ok_inv _ _ _ tail
      cases answer with
      | Err error =>
        simp only [uncurry_apply_pair,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl⟩ := tail
        exact .lowerRejected labelCall live lowerCall
      | Ok unitValue =>
        cases unitValue
        simp only [uncurry_apply_pair, bind_ok] at tail
        obtain ⟨cleared, clearCall, observed⟩ := bind_ok_inv _ _ _ tail
        exact .live labelCall live lowerCall clearCall observed

theorem TableCallbackEffect.observation {A : Type} {ops : runtime.platform.Alloc A}
    {state : Itasca.code.OpIterState} {before after : runtime.compiler.FunctionCompiler A} {fallback}
    (effect : TableCallbackEffect ops state before fallback (.Ok ()) after) :
    ∃ middle, runtime.compiler.FunctionCompiler.observe ops middle state = .ok (.Ok (), after) := by
  cases effect with
  | live labelCall live lowerCall clearCall observed => exact ⟨_, observed⟩
  | dead labelCall dead clearCall observed => exact ⟨_, observed⟩

@[step] theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (depth : U32)
    (fits : before.table_depths.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state depth ⦃ _ => True ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
  step with charge_branch_total ops before.budget as ⟨status, budget⟩
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law budget before.table_depths depth fits

@[step] theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState) (depth : U32)
    (room : before.budget.branches.val < before.budget.limits.max_branch_table_entries.val)
    (capacity : before.table_depths.length < Usize.max) (request : before.table_depths.length + 1 ≤ bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state depth
      ⦃ (status, after) => status = .Ok () ∧ ∃ used,
        after = {before with budget := {before.budget with branches := used}, table_depths := after.table_depths} ∧
        used.val = before.budget.branches.val + 1 ∧ after.table_depths.val = before.table_depths.val ++ [depth] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label
  step with charge_counter_available ops .branches before.budget room
    as ⟨status, budget, accepted, used, same, usedEq⟩
  rw [accepted, same]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available (ChargeCounter.branches.replace before.budget used)
    before.table_depths depth capacity request as ⟨status, budget, depths, accepted, same, appended⟩
  refine ⟨accepted, used, ?_, usedEq, appended⟩
  rw [same]

/-- Callback normality composes label collection, certified live lowering and
observation. The continuation is required only after the default was collected. -/
@[step] theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (fallback : U32) (types : Itasca.signature.ResultType)
    (fits : before.table_depths.val.length < Usize.max)
    (lowerReady : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled) →
      labeled.reachable = true → runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled ⦃ _ => True ⦄) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops before state fallback types ⦃ _ => True ⦄ := by
  obtain ⟨⟨status, labeled⟩, labelCall, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.total ops law before state fallback fits)
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [labelCall, bind_ok]
  cases status with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    cases live : labeled.reachable with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      step with runtime_clear labeled.table_depths as ⟨cleared, empty⟩
      apply WP.spec_mono (compiler_observe ops law {labeled with reachable := false, table_depths := cleared} state)
      intro output post
      trivial
    | true =>
      simp only [ite_true]
      step with lowerReady labeled labelCall live as ⟨answer, lowered⟩
      cases answer with
      | Err error =>
        simp only [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
      | Ok unitValue =>
        cases unitValue
        simp only [bind_ok]
        step with runtime_clear lowered.table_depths as ⟨cleared, empty⟩
        apply WP.spec_mono (compiler_observe ops law {lowered with reachable := false, table_depths := cleared} state)
        intro output post
        trivial

/-- Available table callbacks retain the exact final budget of the chosen
lowering path. Clearing scratch and observing the stack do not charge resources. -/
@[step] theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (before : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (fallback : U32) (types : Itasca.signature.ResultType)
    (room : before.budget.branches.val < before.budget.limits.max_branch_table_entries.val)
    (capacity : before.table_depths.length < Usize.max) (request : before.table_depths.length + 1 ≤ bound)
    (operands : state.vals.length ≤ bound)
    (slots : before.function.local_slots.val + 2 * state.vals.length ≤ U32.max)
    (post : runtime.compiler.FunctionCompiler A → runtime.compiler.FunctionCompiler A → Prop)
    (lowerReady : ∀ labeled,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled) →
      labeled.reachable = true → runtime.compiler.control.FunctionCompiler.lower_table_branches ops labeled
        ⦃ (status, after) => status = .Ok () ∧ post labeled after ∧ after.function.local_slots = before.function.local_slots ⦄) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table ops before state fallback types
      ⦃ (status, after) => status = .Ok () ∧ ∃ labeled,
        runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label ops before state fallback = .ok (.Ok (), labeled) ∧
        if labeled.reachable then ∃ lowered, post labeled lowered ∧ after.budget = lowered.budget
        else after.budget = labeled.budget ⦄ := by
  obtain ⟨⟨status, labeled⟩, labelCall, accepted, _⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.available
      ops bound available before state fallback room capacity request)
  subst status
  have frame := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table_label.inv
    ops before labeled state fallback (.Ok ()) labelCall).frame
  have labeledSlots : labeled.function.local_slots = before.function.local_slots := by rw [frame]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
  rw [labelCall, bind_ok]
  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  cases live : labeled.reachable with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    step with runtime_clear labeled.table_depths as ⟨cleared, empty⟩
    apply WP.spec_mono (compiler_observe_available_budget ops bound available
      {labeled with reachable := false, table_depths := cleared} state operands (by simpa only [labeledSlots] using slots))
    rintro ⟨status, after⟩ ⟨accepted, budget⟩
    refine ⟨accepted, ?_⟩
    simp only [live, Bool.false_eq_true, ite_false]
    exact budget
  | true =>
    simp only [ite_true]
    obtain ⟨⟨status, lowered⟩, lowerCall, accepted, certified, retained⟩ := WP.spec_imp_exists
      (lowerReady labeled labelCall live)
    subst status
    rw [lowerCall, bind_ok]
    simp only [uncurry_apply_pair]
    step with runtime_clear lowered.table_depths as ⟨cleared, empty⟩
    apply WP.spec_mono (compiler_observe_available_budget ops bound available
      {lowered with reachable := false, table_depths := cleared} state operands (by simpa only [retained] using slots))
    rintro ⟨status, after⟩ ⟨accepted, budget⟩
    refine ⟨accepted, ?_⟩
    simp only [live, ite_true]
    exact ⟨lowered, certified, budget⟩

end Itasca.Runtime.Compiler
