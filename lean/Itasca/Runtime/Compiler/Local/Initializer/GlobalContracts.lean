import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Global initialization retains expression compilation and the mapping append separately. -/
inductive InitializerGlobalEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (global : Itasca.metadata.Global) : core.result.Result Unit Itasca.error.VisitError →
    runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop where
  | rejected {error middle afterBudget}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget global.init global.gtype.valtype =
        .ok (.Err error, middle, afterBudget)) :
      InitializerGlobalEffect ops before budget global (.Err error) middle afterBudget
  | appended {index middle expressionBudget status afterBudget indices}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget global.init global.gtype.valtype =
        .ok (.Ok index, middle, expressionBudget))
      (pushed : runtime.compiler.Budget.push ops expressionBudget middle.global_initializers index =
        .ok (status, afterBudget, indices)) :
      InitializerGlobalEffect ops before budget global status {middle with global_initializers := indices} afterBudget

theorem _root_.Itasca.runtime.compiler.initialize.lower_global.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_global ops before budget index = .ok (status, after, afterBudget)) :
    ∃ global, Slice.index_usize before.module.env.globals.deref index = .ok global ∧
      InitializerGlobalEffect ops before budget global status after afterBudget := by
  unfold runtime.compiler.initialize.lower_global at called
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok] at called
  obtain ⟨global, selected, tail⟩ := bind_ok_inv _ _ _ called
  refine ⟨global, selected, ?_⟩
  obtain ⟨⟨expressionStatus, middle, expressionBudget⟩, expressionCalled, tail⟩ := bind_ok_inv _ _ _ tail
  cases expressionStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .rejected expressionCalled
  | Ok functionIndex =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨pushedStatus, pushedBudget, indices⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .appended expressionCalled pushed

theorem InitializerGlobalEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {global status} (effect : InitializerGlobalEffect ops before budget global status after afterBudget) :
    after = {before with functions := after.functions, global_initializers := after.global_initializers} := by
  cases effect with
  | rejected expressionCalled =>
    have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
    rw [same]
  | appended expressionCalled pushed =>
    have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
    rw [same]

theorem InitializerGlobalEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {global status} (effect : InitializerGlobalEffect ops before budget global status after afterBudget)
    (law : Platform.AllocCorrect ops) :
    after.functions.val.length ≤ before.functions.val.length + 1 ∧
    after.global_initializers.val.length ≤ before.global_initializers.val.length + 1 := by
  cases effect with
  | rejected expressionCalled =>
    have expressionEffect := runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled
    refine ⟨expressionEffect.growth law, ?_⟩
    rw [expressionEffect.frame]
    change before.global_initializers.val.length ≤ before.global_initializers.val.length + 1
    omega
  | appended expressionCalled pushed =>
    have expressionEffect := runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled
    have appended := budget_push_code_result ops law _ _ _ _ _ _ pushed
    refine ⟨expressionEffect.growth law, ?_⟩
    rw [expressionEffect.frame] at appended
    rcases appended with same | appended
    · simp only [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem _root_.Itasca.runtime.compiler.initialize.lower_global.inv_selected {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize) (global : Itasca.metadata.Global)
    (found : before.module.env.globals.val[index.val]? = some global)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_global ops before budget index = .ok (status, after, afterBudget)) :
    InitializerGlobalEffect ops before budget global status after afterBudget := by
  obtain ⟨actual, selected, effect⟩ := runtime.compiler.initialize.lower_global.inv
    ops before after budget afterBudget index status called
  have expected := initializer_slice_index before.module.env.globals.deref index global
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)
  rw [expected] at selected
  have same := Result.ok_injective selected
  subst actual
  exact effect

theorem InitializerGlobalEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {global} (effect : InitializerGlobalEffect ops before budget global (.Ok ()) after afterBudget)
    (law : Platform.AllocCorrect ops) :
    ∃ function functionIndex, InitializerCode function global.init global.gtype.valtype ∧
      functionIndex.val = before.functions.val.length ∧
      after = {before with functions := after.functions, global_initializers := after.global_initializers} ∧
      after.functions.val = before.functions.val ++ [function] ∧
      after.global_initializers.val = before.global_initializers.val ++ [functionIndex] := by
  cases effect with
  | appended expressionCalled pushed =>
    obtain ⟨function, certified, indexEq, frame, appended⟩ :=
      (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).success law
    have pushedValues := (budget_push_success ops law _ _ _ _ _ pushed).2
    refine ⟨function, _, certified, indexEq, ?_, appended, ?_⟩
    · rw [frame]
    · rw [frame] at pushedValues
      exact pushedValues

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_global.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (global : Itasca.metadata.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (functionsFit : module.functions.length < Usize.max)
    (initializersFit : module.global_initializers.length < Usize.max) :
    runtime.compiler.initialize.lower_global ops module budget index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  rw [initializer_slice_index module.module.env.globals.deref index global
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found), bind_ok]
  obtain ⟨⟨status, middle, expressionBudget⟩, expressionCalled, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.expression.total ops law module budget global.init global.gtype.valtype functionsFit)
  rw [expressionCalled, bind_ok]
  simp only [uncurry_apply_pair]
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok functionIndex =>
    have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
    have fits : middle.global_initializers.length < Usize.max := by rw [same]; exact initializersFit
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law expressionBudget middle.global_initializers functionIndex fits
      as ⟨status, afterBudget, initializers, changed⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_global.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (global : Itasca.metadata.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (vector : ∀ lo hi, global.init = .V128 lo hi → global.gtype.valtype = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (functionsRequest : module.functions.length + 1 ≤ bound) (functionsFit : module.functions.length < Usize.max)
    (initializersRequest : module.global_initializers.length + 1 ≤ bound)
    (initializersFit : module.global_initializers.length < Usize.max) :
    runtime.compiler.initialize.lower_global ops module budget index ⦃ (status, after, afterBudget) =>
      status = .Ok () ∧ afterBudget.instructions.val = budget.instructions.val + 2 ∧
      afterBudget.limits = budget.limits ∧
      after = {module with functions := after.functions, global_initializers := after.global_initializers} ∧
      after.global_initializers.val = module.global_initializers.val ++ [alloc.vec.Vec.len module.functions] ∧
      ∃ function, InitializerCode function global.init global.gtype.valtype ∧
        after.functions.val = module.functions.val ++ [function] ⦄ := by
  unfold runtime.compiler.initialize.lower_global
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
  rw [initializer_slice_index module.module.env.globals.deref index global
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found), bind_ok]
  step with runtime.compiler.initialize.expression.available ops bound available module budget
    global.init global.gtype.valtype vector instructions codeRequest functionsRequest functionsFit
    as ⟨status, middle, expressionBudget, accepted, count, limits, function, certified, appended, frame⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have sameInitializers : middle.global_initializers = module.global_initializers := by rw [frame]
  step with budget_push_available ops bound available expressionBudget middle.global_initializers
    (alloc.vec.Vec.len module.functions) (by rw [sameInitializers]; exact initializersFit)
    (by rw [sameInitializers]; exact initializersRequest)
    as ⟨status, afterBudget, indices, accepted, budgetEq, pushed⟩
  refine ⟨accepted, ?_, ?_, ?_, ?_, function, certified, appended⟩
  · rw [budgetEq]
    exact count
  · rw [budgetEq]
    exact limits
  · rw [frame]
  · simpa only [sameInitializers] using pushed

end Itasca.Runtime.Compiler
