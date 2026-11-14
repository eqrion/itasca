import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Active data offsets may compile code before publishing their mapping; passive
segments publish an absent offset directly. Both retain rejected append states. -/
inductive InitializerDataOffsetEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    Itasca.metadata.DataMode → core.result.Result Unit Itasca.error.VisitError →
    runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop where
  | rejected {memory offset error middle afterBudget}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget offset .I32 =
        .ok (.Err error, middle, afterBudget)) :
      InitializerDataOffsetEffect ops before budget (.Active memory offset) (.Err error) middle afterBudget
  | active {memory offset functionIndex middle expressionBudget status afterBudget indices}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget offset .I32 =
        .ok (.Ok functionIndex, middle, expressionBudget))
      (pushed : runtime.compiler.Budget.push ops expressionBudget middle.data_offsets (some functionIndex) =
        .ok (status, afterBudget, indices)) :
      InitializerDataOffsetEffect ops before budget (.Active memory offset) status
        {middle with data_offsets := indices} afterBudget
  | passive {status afterBudget indices}
      (pushed : runtime.compiler.Budget.push ops budget before.data_offsets none = .ok (status, afterBudget, indices)) :
      InitializerDataOffsetEffect ops before budget .Passive status {before with data_offsets := indices} afterBudget

theorem _root_.Itasca.runtime.compiler.initialize.lower_data_offset.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_data_offset ops before budget index = .ok (status, after, afterBudget)) :
    ∃ segment, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.metadata.Data)
      before.module.tail.data index = .ok segment ∧
      InitializerDataOffsetEffect ops before budget segment.mode status after afterBudget := by
  unfold runtime.compiler.initialize.lower_data_offset at called
  simp only [runtime.compiler.ExecutableModule.tail.eq, Itasca.metadata.Module.impl.tail, bind_ok] at called
  obtain ⟨segment, selected, tail⟩ := bind_ok_inv _ _ _ called
  refine ⟨segment, selected, ?_⟩
  cases mode : segment.mode with
  | Active memory offset =>
    rw [mode] at tail
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
      exact .active expressionCalled pushed
  | Passive =>
    rw [mode] at tail
    obtain ⟨⟨pushedStatus, pushedBudget, indices⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .passive pushed

theorem InitializerDataOffsetEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {mode status} (effect : InitializerDataOffsetEffect ops before budget mode status after afterBudget) :
    after = {before with functions := after.functions, data_offsets := after.data_offsets} := by
  cases effect with
  | rejected expressionCalled =>
    have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
    rw [same]
  | active expressionCalled pushed =>
    have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
    rw [same]
  | passive pushed => rfl

theorem InitializerDataOffsetEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {mode status} (effect : InitializerDataOffsetEffect ops before budget mode status after afterBudget)
    (law : Platform.AllocCorrect ops) :
    after.functions.val.length ≤ before.functions.val.length + 1 ∧
    after.data_offsets.val.length ≤ before.data_offsets.val.length + 1 := by
  cases effect with
  | rejected expressionCalled =>
    have expressionEffect := runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled
    refine ⟨expressionEffect.growth law, ?_⟩
    rw [expressionEffect.frame]
    change before.data_offsets.val.length ≤ before.data_offsets.val.length + 1
    omega
  | active expressionCalled pushed =>
    have expressionEffect := runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled
    have appended := budget_push_code_result ops law _ _ _ _ _ _ pushed
    refine ⟨expressionEffect.growth law, ?_⟩
    rw [expressionEffect.frame] at appended
    rcases appended with same | appended
    · simp only [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]
  | passive pushed =>
    have appended := budget_push_code_result ops law _ _ _ _ _ _ pushed
    refine ⟨?_, ?_⟩
    · change before.functions.val.length ≤ before.functions.val.length + 1
      omega
    rcases appended with same | appended
    · simp only [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem _root_.Itasca.runtime.compiler.initialize.lower_data_offset.inv_selected {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize) (segment : Itasca.metadata.Data)
    (found : before.module.tail.data.val[index.val]? = some segment)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_data_offset ops before budget index = .ok (status, after, afterBudget)) :
    InitializerDataOffsetEffect ops before budget segment.mode status after afterBudget := by
  obtain ⟨actual, selected, effect⟩ := runtime.compiler.initialize.lower_data_offset.inv
    ops before after budget afterBudget index status called
  rw [initializer_vec_index _ _ segment found] at selected
  have same := Result.ok_injective selected
  subst actual
  exact effect

theorem InitializerDataOffsetEffect.active_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {memory offset}
    (effect : InitializerDataOffsetEffect ops before budget (.Active memory offset) (.Ok ()) after afterBudget)
    (law : Platform.AllocCorrect ops) :
    ∃ function functionIndex, InitializerCode function offset .I32 ∧
      functionIndex.val = before.functions.val.length ∧
      after = {before with functions := after.functions, data_offsets := after.data_offsets} ∧
      after.functions.val = before.functions.val ++ [function] ∧
      after.data_offsets.val = before.data_offsets.val ++ [some functionIndex] := by
  cases effect with
  | active expressionCalled pushed =>
    obtain ⟨function, certified, indexEq, frame, appended⟩ :=
      (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).success law
    have pushedValues := (budget_push_success ops law _ _ _ _ _ pushed).2
    refine ⟨function, _, certified, indexEq, ?_, appended, ?_⟩
    · rw [frame]
    · rw [frame] at pushedValues
      exact pushedValues

theorem InitializerDataOffsetEffect.passive_success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    (effect : InitializerDataOffsetEffect ops before budget .Passive (.Ok ()) after afterBudget)
    (law : Platform.AllocCorrect ops) :
    after = {before with data_offsets := after.data_offsets} ∧
      after.data_offsets.val = before.data_offsets.val ++ [none] := by
  cases effect with
  | passive pushed => exact ⟨rfl, (budget_push_success ops law _ _ _ _ _ pushed).2⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_data_offset.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (functionsFit : module.functions.length < Usize.max)
    (offsetsFit : module.data_offsets.length < Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops module budget index ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.lower_data_offset
  simp only [runtime.compiler.ExecutableModule.tail.eq, Itasca.metadata.Module.impl.tail, bind_ok]
  rw [initializer_vec_index _ _ segment found, bind_ok]
  cases mode : segment.mode with
  | Active memory offset =>
    simp only [mode]
    obtain ⟨⟨status, middle, expressionBudget⟩, expressionCalled, normal⟩ := WP.spec_imp_exists
      (runtime.compiler.initialize.expression.total ops law module budget offset .I32 functionsFit)
    rw [expressionCalled, bind_ok]
    simp only [uncurry_apply_pair]
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
    | Ok functionIndex =>
      have same := (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
      have fits : middle.data_offsets.length < Usize.max := by rw [same]; exact offsetsFit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law expressionBudget middle.data_offsets (some functionIndex) fits
        as ⟨status, afterBudget, offsets, changed⟩
  | Passive =>
    step with budget_push ops law budget module.data_offsets none offsetsFit
      as ⟨status, afterBudget, offsets, changed⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_data_offset.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (scalar : ∀ memory offset, segment.mode = .Active memory offset → ∀ lo hi, offset ≠ .V128 lo hi)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (functionsRequest : module.functions.length + 1 ≤ bound) (functionsFit : module.functions.length < Usize.max)
    (offsetsRequest : module.data_offsets.length + 1 ≤ bound) (offsetsFit : module.data_offsets.length < Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops module budget index ⦃ (status, after, afterBudget) =>
      status = .Ok () ∧ afterBudget.instructions.val ≤ budget.instructions.val + 2 ∧
      afterBudget.limits = budget.limits ∧
      after = {module with functions := after.functions, data_offsets := after.data_offsets} ∧
      after.functions.val.length ≤ module.functions.val.length + 1 ∧
      after.data_offsets.val.length = module.data_offsets.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.lower_data_offset
  simp only [runtime.compiler.ExecutableModule.tail.eq, Itasca.metadata.Module.impl.tail, bind_ok]
  rw [initializer_vec_index _ _ segment found, bind_ok]
  cases mode : segment.mode with
  | Active memory offset =>
    step with runtime.compiler.initialize.expression.available ops bound available module budget offset .I32
      (fun lo hi matching => False.elim (scalar memory offset mode lo hi matching))
      instructions codeRequest functionsRequest functionsFit
      as ⟨status, middle, expressionBudget, accepted, count, limits, function, certified, appended, frame⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have sameOffsets : middle.data_offsets = module.data_offsets := by rw [frame]
    step with budget_push_available ops bound available expressionBudget middle.data_offsets
      (some (alloc.vec.Vec.len module.functions)) (by rw [sameOffsets]; exact offsetsFit)
      (by rw [sameOffsets]; exact offsetsRequest)
      as ⟨status, afterBudget, offsets, accepted, budgetEq, pushed⟩
    refine ⟨accepted, ?_, ?_, ?_, ?_, ?_⟩
    · rw [budgetEq, count]
    · rw [budgetEq]
      exact limits
    · rw [frame]
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]
    · simpa only [sameOffsets, List.length_append, List.length_singleton] using congrArg List.length pushed
  | Passive =>
    step with budget_push_available ops bound available budget module.data_offsets none offsetsFit offsetsRequest
      as ⟨status, afterBudget, offsets, accepted, budgetEq, pushed⟩
    refine ⟨accepted, ?_, ?_, ?_, ?_⟩
    · rw [budgetEq]
      omega
    · rw [budgetEq]
    · omega
    · simpa only [List.length_append, List.length_singleton] using congrArg List.length pushed

end Itasca.Runtime.Compiler
