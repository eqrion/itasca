import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Lowering.Emission.LoweringEmpty
import Itasca.Module.Const.Parser

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects GlobalAndDataContracts, ModuleContracts, MappingConstruction, SegmentEmissionContracts.
Each section documents its contracts and consumers.
-/

/-! ## GlobalAndDataContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects GlobalContracts, DataOffsetContracts.
Each section documents its contracts and consumers.
-/

/-! ## GlobalContracts -/

section

/-!
# Global initializer contracts

Global lowering separates expression compilation from its mapping append, retaining their success and error effects. Module initializer traversal composes these local contracts.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.globals, bind_ok] at called
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
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.globals, bind_ok]
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
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.globals, bind_ok]
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

end Itasca.Compiler

end

/-! ## DataOffsetContracts -/

section

open Itasca.Representation

/-!
# Data-offset lowering contracts

Active offsets compile an initializer before publishing their mapping; passive segments publish an absent offset. The contracts retain the exact state of rejected mapping appends.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

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
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok] at called
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
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
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
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
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

end Itasca.Compiler

end

end

/-! ## ModuleContracts -/

section

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects ElementContracts, ModuleLoopContracts.
Each section documents its contracts and consumers.
-/

/-! ## ElementContracts -/

section

open Itasca.Representation

/-!
# Element-segment lowering

Collected initializer values and their published row precede offset compilation. The segment contract preserves this ordering and the exact retained prefix on refusal.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

theorem element_offset_found (env : Itasca.metadata.Env) (index : Usize)
    (segment : Itasca.metadata.Element) (found : env.elements.val[index.val]? = some segment) :
    runtime.compiler.initialize.element_offset env index = .ok (sourceElementOffset segment) := by
  unfold runtime.compiler.initialize.element_offset
  simp only [Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  unfold sourceElementOffset
  cases segment.mode <;> rfl

/-- The successfully collected values and published row preceding offset compilation. -/
structure InitializerElementPrefix {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize) where
  middle : runtime.compiler.ExecutableModule
  collected : runtime.compiler.Budget A
  charged : runtime.compiler.Budget A
  indices : alloc.vec.Vec Usize
  rows : alloc.vec.Vec (alloc.vec.Vec Usize)
  loopCalled : runtime.compiler.initialize.lower_element_loop ops before budget index
    (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, collected, indices, .Ok ())
  rowCalled : runtime.compiler.Budget.push ops collected middle.element_initializers indices =
    .ok (.Ok (), charged, rows)

def InitializerElementPrefix.result {A : Type} {ops : runtime.platform.Alloc A}
    {before : runtime.compiler.ExecutableModule} {budget : runtime.compiler.Budget A} {index : Usize}
    (stages : InitializerElementPrefix ops before budget index) : runtime.compiler.ExecutableModule :=
  {stages.middle with element_initializers := stages.rows}

/-- Every normally returned element initializer retains its exact completed stages,
including rows published before an offset error. -/
inductive InitializerElementEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop
  | loopRejected (middle charged indices error)
      (called : runtime.compiler.initialize.lower_element_loop ops before budget index
        (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, charged, indices, .Err error)) :
      InitializerElementEffect ops before budget index (.Err error) middle charged
  | rowRejected (middle collected charged indices rows error)
      (loopCalled : runtime.compiler.initialize.lower_element_loop ops before budget index
        (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, collected, indices, .Ok ()))
      (rowCalled : runtime.compiler.Budget.push ops collected middle.element_initializers indices =
        .ok (.Err error, charged, rows)) :
      InitializerElementEffect ops before budget index (.Err error) {middle with element_initializers := rows} charged
  | absent (stages : InitializerElementPrefix ops before budget index) (status charged offsets)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok none)
      (called : runtime.compiler.Budget.push ops stages.charged stages.middle.element_offsets none =
        .ok (status, charged, offsets)) :
      InitializerElementEffect ops before budget index status {stages.result with element_offsets := offsets} charged
  | expressionRejected (stages : InitializerElementPrefix ops before budget index) (expr middle charged error)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok (some expr))
      (called : runtime.compiler.initialize.expression ops stages.result stages.charged expr .I32 =
        .ok (.Err error, middle, charged)) :
      InitializerElementEffect ops before budget index (.Err error) middle charged
  | present (stages : InitializerElementPrefix ops before budget index) (expr middle expressionBudget value status charged offsets)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok (some expr))
      (expressionCalled : runtime.compiler.initialize.expression ops stages.result stages.charged expr .I32 =
        .ok (.Ok value, middle, expressionBudget))
      (called : runtime.compiler.Budget.push ops expressionBudget middle.element_offsets (some value) =
        .ok (status, charged, offsets)) :
      InitializerElementEffect ops before budget index status {middle with element_offsets := offsets} charged

theorem _root_.Itasca.runtime.compiler.initialize.lower_element.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element ops before budget index = .ok (status, after, afterBudget)) :
    InitializerElementEffect ops before budget index status after afterBudget := by
  unfold runtime.compiler.initialize.lower_element at called
  obtain ⟨⟨middle, collected, indices, loopStatus⟩, loopCalled, tail⟩ := bind_ok_inv _ _ _ called
  cases loopStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .loopRejected middle collected indices error loopCalled
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨rowStatus, charged, rows⟩, rowCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases rowStatus with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .rowRejected middle collected charged indices rows error loopCalled rowCalled
    | Ok unitValue =>
      cases unitValue
      let stages : InitializerElementPrefix ops before budget index :=
        ⟨middle, collected, charged, indices, rows, loopCalled, rowCalled⟩
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env.eq, bind_ok] at tail
      obtain ⟨offset, read, tail⟩ := bind_ok_inv _ _ _ tail
      cases offset with
      | none =>
        obtain ⟨⟨result, finalBudget, offsets⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .absent stages result finalBudget offsets read pushed
      | some expr =>
        obtain ⟨⟨expressionStatus, final, expressionBudget⟩, expressionCalled, tail⟩ := bind_ok_inv _ _ _ tail
        cases expressionStatus with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .expressionRejected stages expr final expressionBudget error read expressionCalled
        | Ok value =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
          obtain ⟨⟨result, finalBudget, offsets⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .present stages expr final expressionBudget value result finalBudget offsets read expressionCalled pushed

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (space : initializerSize m + segment.init.val.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops m budget i ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + segment.init.val.length + 3 ⦄ := by
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_total ops law m budget i (alloc.vec.Vec.new _) 0#usize
    (.Ok ()) segment found (by simp) (by simp) (by simpa using (show initializerSize m + segment.init.val.length ≤ Usize.max by omega))
    as ⟨middle, b1, indices, status, same, size⟩
  change initializerSize middle ≤ initializerSize m + segment.init.val.length at size
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_push_total ops law b1 middle.element_initializers indices
      (by unfold initializerSize at size space; omega) as ⟨status, b2, rows, rowsBound⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        runtime.compiler.ExecutableModule.env.eq,
        Itasca.metadata.Module.impl.env, runtime.compiler.initialize.element_offset, Itasca.metadata.Env.impl.elements]
      try simp only [bind_ok]
      rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref, same] using found), bind_ok]
      have room : initializerSize { middle with element_initializers := rows } + 2 ≤ Usize.max := by
        unfold initializerSize at *; dsimp at *; omega
      have middleSize : initializerSize { middle with element_initializers := rows } ≤
          initializerSize m + segment.init.val.length + 1 := by
        unfold initializerSize at *; dsimp at *; omega
      cases mode : segment.mode with
      | Active table offset =>
        simp only [mode, bind_ok]
        step with initializer_expression_total ops law { middle with element_initializers := rows }
          b2 offset .I32 (by omega) as ⟨status, final, b3, source, growth⟩
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
          exact ⟨source.trans same, by omega⟩
        | Ok index =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_push_total ops law b3 final.element_offsets (some index)
            (by unfold initializerSize at room growth; omega) as ⟨status, b4, offsets, offsetsBound⟩
          exact ⟨source.trans same, by unfold initializerSize at *; dsimp at *; omega⟩
      | Passive | Declarative =>
        simp only [mode, bind_ok]
        step with initializer_push_total ops law b2 middle.element_offsets none
          (by unfold initializerSize at room; dsimp at room; omega) as ⟨status, b3, offsets, offsetsBound⟩
        exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩

/-- Source typing and independent retained/scratch demand for one element mapping. -/
structure InitializerElementDemand {A : Type} (bound : Nat) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize) (segment : Itasca.metadata.Element) where
  lookup : module.module.env.elements.val[index.val]? = some segment
  typed : ∀ expr ∈ segment.init.val, Itasca.Module.Constants.Valid module.module.env expr
      (Itasca.Module.Constants.referenceValueType segment.elem)
  offsetTyped : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 2*segment.init.length + 2 ≤ budget.limits.max_instructions.val
  codeRequest : 2 ≤ bound
  reserve : initializerSize module + segment.init.length + 3 ≤ bound
  capacity : initializerSize module + segment.init.length + 3 ≤ Usize.max

theorem _root_.Itasca.runtime.compiler.initialize.lower_element.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Element)
    (demand : InitializerElementDemand bound module budget index segment) :
    runtime.compiler.initialize.lower_element ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2*segment.init.length + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + segment.init.length + 3 ⦄ := by
  rcases demand with ⟨lookup, typed, offsetTyped, instructions, codeRequest, reserve, capacity⟩
  have initLength : segment.init.length = segment.init.val.length := rfl
  simp only [alloc.vec.Vec.length] at instructions reserve capacity ⊢
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_available ops bound available module budget (alloc.vec.Vec.new _) index
    0#usize segment lookup (by simp) typed (by simpa [alloc.vec.Vec.length] using (show
      budget.instructions.val + 2*segment.init.length ≤ budget.limits.max_instructions.val by omega)) codeRequest
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ bound by omega))
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ bound by omega))
    as ⟨middle,charged,indices,status,accepted,same,limits,size,indexSize,used⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have sizeBound : initializerSize middle + 3 ≤ bound := by change initializerSize middle + 3 ≤ bound; omega
  have sizeCapacity : initializerSize middle + 3 ≤ Usize.max := by omega
  step with budget_push_available ops bound available charged middle.element_initializers indices
    (by simp only [initializerSize] at sizeCapacity; omega)
    (by simp only [initializerSize] at sizeBound; omega)
    as ⟨status,rowBudget,rows,accepted,sameBudget,appended⟩
  subst status rowBudget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env]
  rw [same,element_offset_found module.module.env index segment lookup,bind_ok]
  have rowSize : initializerSize {middle with module := module.module, element_initializers := rows} = initializerSize middle + 1 := by
    simp only [initializerSize,appended,List.length_append,List.length_singleton]
    omega
  generalize offsetEq : sourceElementOffset segment = offset
  cases offset with
  | none =>
    step with budget_push_available ops bound available charged middle.element_offsets none
      (by simp only [initializerSize] at sizeCapacity; omega)
      (by simp only [initializerSize] at sizeBound; omega)
      as ⟨status,afterBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_⟩
    · simpa [sameBudget,used] using (show charged.instructions.val ≤ budget.instructions.val + 2*segment.init.length+2 by omega)
    · simpa [sameBudget] using limits
    · simp only [initializerSize,appended,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at size
      omega
  | some expr =>
    have valid : Itasca.Module.Constants.Valid module.module.env expr .I32 := by
      unfold sourceElementOffset at offsetEq
      cases mode : segment.mode with
      | Passive => simp [mode] at offsetEq
      | Declarative => simp [mode] at offsetEq
      | Active table offset =>
        simp only [mode,Option.some.injEq] at offsetEq
        subst expr
        exact offsetTyped table offset mode
    have functionBound : middle.functions.length ≤ initializerSize middle := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with runtime.compiler.initialize.expression.available ops bound available {middle with module := module.module, element_initializers := rows} charged expr .I32
      (by intro lo hi matching; rw [matching] at valid; cases valid) (by rw [limits]; omega) codeRequest
      (by change middle.functions.length + 1 ≤ bound; omega)
      (by change middle.functions.length < Usize.max; omega)
      as ⟨status,afterExpression,afterBudget,accepted,usedAgain,limitsAgain,function,shape,emitted,sameExpression⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have expressionSize : initializerSize afterExpression = initializerSize middle + 2 := by
      rw [sameExpression]
      simp only [initializerSize,emitted,List.length_append,List.length_singleton] at rowSize ⊢
      omega
    have offsetBound : afterExpression.element_offsets.length ≤ initializerSize afterExpression := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with budget_push_available ops bound available afterBudget afterExpression.element_offsets _
      (by change afterExpression.element_offsets.length < Usize.max; omega)
      (by change afterExpression.element_offsets.length + 1 ≤ bound; omega)
      as ⟨status,finalBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_,?_⟩
    · simpa [sameBudget] using (show afterBudget.instructions.val ≤ budget.instructions.val+2*segment.init.length+2 by omega)
    · simpa [sameBudget,limitsAgain] using limits
    · exact congrArg (fun value => value.module) sameExpression
    · simp only [initializerSize,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at expressionSize size
      omega

/-- Normal element-value loop returns preserve the executable source module. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.source {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (status result : core.result.Result Unit Itasca.error.VisitError)
    (segment : Itasca.metadata.Element) (found : before.module.env.elements.val[i.val]? = some segment)
    (bounded : j.val ≤ segment.init.val.length)
    (called : runtime.compiler.initialize.lower_element_loop ops before budget i indices j status =
      .ok (after, afterBudget, outIndices, result)) : after.module = before.module := by
  apply runtime.compiler.initialize.lower_element_loop.inv
    { ops := ops, before := before, budget := budget, indices := indices, i := i, j := j,
      status := status, segment := segment, found := found, bounded := bounded,
      P := fun _ _ _ _ _ => True, Q := fun current _ _ _ => current.module = before.module,
      advance := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro,
      finish := fun _ _ _ _ _ source _ _ _ => source, initial := True.intro }
    after afterBudget outIndices result called

/-- Even partial element publication preserves the executable source module. -/
theorem InitializerElementEffect.source {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {index : Usize} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : InitializerElementEffect ops before budget index status after afterBudget)
    (segment : Itasca.metadata.Element) (found : before.module.env.elements.val[index.val]? = some segment) :
    after.module = before.module := by
  have loopSource : ∀ middle charged indices result,
      runtime.compiler.initialize.lower_element_loop ops before budget index (alloc.vec.Vec.new _) 0#usize (.Ok ()) =
        .ok (middle, charged, indices, result) → middle.module = before.module := by
    intro middle charged indices result called
    exact runtime.compiler.initialize.lower_element_loop.source ops before middle budget charged
      (alloc.vec.Vec.new _) indices index 0#usize (.Ok ()) result segment found (by change 0 ≤ _; omega) called
  cases effect with
  | loopRejected middle charged indices error called => exact loopSource after afterBudget indices (.Err error) called
  | rowRejected middle collected charged indices rows error called pushed =>
    exact loopSource middle collected indices (.Ok ()) called
  | absent stages status charged offsets read pushed =>
    exact loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled
  | expressionRejected stages expr middle charged error read called =>
    have expression := runtime.compiler.initialize.expression.inv ops stages.result after stages.charged afterBudget expr .I32 (.Err error) called
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) expression.frame
    exact source.trans (loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled)
  | present stages expr middle expressionBudget value status charged offsets read called pushed =>
    have expression := runtime.compiler.initialize.expression.inv ops stages.result middle stages.charged expressionBudget expr .I32 (.Ok value) called
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) expression.frame
    exact source.trans (loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled)

end Itasca.Compiler

end

/-! ## ModuleLoopContracts -/

section

/-!
# Module initializer traversal

A common indexed traversal covers global, element and data mappings. Its callback and loop relations retain source-module identity and actual error states.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

private abbrev InitializerStatus := core.result.Result Unit Itasca.error.VisitError
private abbrev ModuleInitializerState (A : Type) := runtime.compiler.ExecutableModule ×
  runtime.compiler.Budget A × Usize × InitializerStatus
private abbrev ModuleInitializerResult (A : Type) := runtime.compiler.ExecutableModule ×
  runtime.compiler.Budget A × InitializerStatus

/-- The common indexed traversal shared by global, element and data mapping loops.
The callback preserves the source module even when returning an error. -/
structure InitializerModuleLoop (A : Type) where
  body : ModuleInitializerState A → Result (ControlFlow (ModuleInitializerState A) (ModuleInitializerResult A))
  callback : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Usize →
    Result (InitializerStatus × runtime.compiler.ExecutableModule × runtime.compiler.Budget A)
  length : Itasca.metadata.Module → Usize
  body_eq : ∀ current charged cursor result count, length current.module = count →
    body (current, charged, cursor, result) =
      if cursor < count then
        match result with
        | .Err _ => .ok (.done (current, charged, result))
        | .Ok () => do
          let (result, next, nextBudget) ← callback current charged cursor
          let nextIndex ← cursor + 1#usize
          Result.ok (.cont (next, nextBudget, nextIndex, result))
      else .ok (.done (current, charged, result))
  callback_frame : ∀ current next charged nextBudget cursor result,
    cursor.val < (length current.module).val →
    callback current charged cursor = .ok (result, next, nextBudget) → next.module = current.module

/-- All normal loop returns transport any callback-preserved predicate. Source
identity and cursor bounds are maintained by the loop contract itself. -/
structure ModuleLoopInvariant (A : Type) where
  rules : InitializerModuleLoop A
  before : runtime.compiler.ExecutableModule
  budget : runtime.compiler.Budget A
  j : Usize
  status : core.result.Result Unit Itasca.error.VisitError
  length : Usize
  lengthEq : rules.length before.module = length
  P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A →
      core.result.Result Unit Itasca.error.VisitError → Prop
  advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize),
      current.module = before.module → cursor.val < length.val → P current charged cursor (.Ok ()) →
      ∀ result next nextBudget (nextIndex : Usize),
        rules.callback current charged cursor =
          .ok (result, next, nextBudget) → nextIndex.val = cursor.val + 1 →
        P next nextBudget nextIndex result
  finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → P current charged cursor result →
      (length.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q current charged result
  initial : P before budget j status

theorem InitializerModuleLoop.inv {A : Type} (context : ModuleLoopInvariant A)
    (after : runtime.compiler.ExecutableModule) (afterBudget : runtime.compiler.Budget A)
    (result : core.result.Result Unit Itasca.error.VisitError)
    (called : loop context.rules.body (context.before, context.budget, context.j, context.status) =
      .ok (after, afterBudget, result)) : context.Q after afterBudget result := by
  rcases context with ⟨rules, before, budget, j, status, length, lengthEq, P, Q, advance, finish, initial⟩
  let measure : ModuleInitializerState A → Nat := fun (_, _, cursor, _) =>
    length.val - cursor.val
  let invariant : ModuleInitializerState A → Prop := fun (current, charged, cursor, result) =>
    current.module = before.module ∧ P current charged cursor result
  apply initializer_loop_success _ measure invariant
    (fun (current, charged, result) => Q current charged result) ?_ _ ⟨rfl, initial⟩ _ called
  rintro ⟨current, charged, cursor, result⟩ ⟨source, prior⟩ flow body
  have selected : rules.length current.module = length := by rw [source, lengthEq]
  simp only [rules.body_eq current charged cursor result length selected] at body
  by_cases more : cursor < length
  · rw [if_pos more] at body
    have inside : cursor.val < length.val := by scalar_tac
    cases result with
    | Err error =>
      have output := Result.ok_injective body
      subst flow
      exact finish current charged cursor (.Err error) source prior (.inr (by intro impossible; cases impossible))
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨nextResult, next, nextBudget⟩, lowered, tail⟩ := bind_ok_inv _ _ _ body
      obtain ⟨nextIndex, added, tail⟩ := bind_ok_inv _ _ _ tail
      have output := Result.ok_injective tail
      subst flow
      have increment : cursor + 1#usize ⦃ next => next.val = cursor.val + 1 ⦄ := by
        step as ⟨next, nextEq⟩
        scalar_tac
      rw [added] at increment
      simp only [WP.spec_ok] at increment
      have nextSource := rules.callback_frame current next charged nextBudget cursor nextResult (by simpa only [selected] using inside) lowered
      refine ⟨⟨nextSource.trans source, advance current charged cursor source inside prior
        nextResult next nextBudget nextIndex lowered increment⟩, ?_⟩
      dsimp only [measure]
      omega
  · rw [if_neg more] at body
    have output := Result.ok_injective body
    subst flow
    have last : length.val ≤ cursor.val := by
      have notInside : ¬ cursor.val < length.val := by scalar_tac
      omega
    exact finish current charged cursor result source prior (.inl last)

/-- Normal loop execution follows any normally returning callback contract.
The callback postcondition may express exact mappings or resource bounds. -/
structure ModuleLoopTotal (A : Type) where
  rules : InitializerModuleLoop A
  before : runtime.compiler.ExecutableModule
  budget : runtime.compiler.Budget A
  j : Usize
  status : core.result.Result Unit Itasca.error.VisitError
  length : Usize
  lengthEq : rules.length before.module = length
  P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A →
      core.result.Result Unit Itasca.error.VisitError → Prop
  advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize),
      current.module = before.module → cursor.val < length.val → P current charged cursor (.Ok ()) →
      rules.callback current charged cursor
        ⦃ (result, next, nextBudget) => ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndex result ⦄
  finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → P current charged cursor result →
      (length.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q current charged result
  initial : P before budget j status

@[step] theorem InitializerModuleLoop.total {A : Type} (context : ModuleLoopTotal A) :
    loop context.rules.body (context.before, context.budget, context.j, context.status)
      ⦃ (after, afterBudget, result) => context.Q after afterBudget result ⦄ := by
  rcases context with ⟨rules, before, budget, j, status, length, lengthEq, P, Q, advance, finish, initial⟩
  let measure : ModuleInitializerState A → Nat := fun (_, _, cursor, _) =>
    length.val - cursor.val
  let invariant : ModuleInitializerState A → Prop := fun (current, charged, cursor, result) =>
    current.module = before.module ∧ P current charged cursor result
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨current, charged, cursor, result⟩ ⟨source, prior⟩
    have selected : rules.length current.module = length := by rw [source, lengthEq]
    simp only [rules.body_eq current charged cursor result length selected]
    by_cases more : cursor < length
    · rw [if_pos more]
      have inside : cursor.val < length.val := by scalar_tac
      cases result with
      | Err error =>
        exact WP.spec.ret (finish current charged cursor (.Err error) source prior
          (.inr (by intro impossible; cases impossible)))
      | Ok unitValue =>
        cases unitValue
        obtain ⟨⟨nextResult, next, nextBudget⟩, lowered, post⟩ := WP.spec_imp_exists
          (advance current charged cursor source inside prior)
        simp only [lowered, bind_ok, uncurry_apply_pair]
        have nextSource := rules.callback_frame current next charged nextBudget cursor nextResult (by simpa only [selected] using inside) lowered
        step as ⟨nextIndex, increment⟩
        refine ⟨⟨nextSource.trans source, post nextIndex (by scalar_tac)⟩, ?_⟩
        dsimp only [measure]
        scalar_tac
    · rw [if_neg more]
      have last : length.val ≤ cursor.val := by
        have notInside : ¬ cursor.val < length.val := by scalar_tac
        omega
      exact WP.spec.ret (finish current charged cursor result source prior (.inl last))
  · exact ⟨rfl, initial⟩

/-- A successful callback at every remaining source index yields a successful
loop. The caller supplies its exact invariant and final postcondition. -/
structure ModuleLoopAvailable (A : Type) where
  rules : InitializerModuleLoop A
  before : runtime.compiler.ExecutableModule
  budget : runtime.compiler.Budget A
  j : Usize
  length : Usize
  lengthEq : rules.length before.module = length
  bounded : j.val ≤ length.val
  P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Usize → Prop
  Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop
  advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize), current.module = before.module →
      cursor.val < length.val → P current charged cursor →
      rules.callback current charged cursor
        ⦃ (result, next, nextBudget) => result = .Ok () ∧ ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndex ⦄
  finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (cursor : Usize), current.module = before.module →
      cursor.val = length.val → P current charged cursor → Q current charged
  initial : P before budget j

@[step] theorem InitializerModuleLoop.available {A : Type} (context : ModuleLoopAvailable A) :
    loop context.rules.body (context.before, context.budget, context.j, .Ok ())
      ⦃ (after, afterBudget, result) => result = .Ok () ∧ context.Q after afterBudget ⦄ := by
  rcases context with ⟨rules, before, budget, j, length, lengthEq, bounded, P, Q, advance, finish, initial⟩
  apply InitializerModuleLoop.total
    { rules := rules, before := before, budget := budget, j := j, status := .Ok (),
      length := length, lengthEq := lengthEq,
      P := fun current charged cursor result => result = .Ok () ∧ cursor.val ≤ length.val ∧ P current charged cursor,
      Q := fun current charged result => result = .Ok () ∧ Q current charged,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source inside prior
    apply WP.spec_mono (advance current charged cursor source inside prior.2.2)
    rintro ⟨result, next, nextBudget⟩ ⟨accepted, post⟩ nextIndex increment
    exact ⟨accepted, by omega, post nextIndex increment⟩
  · intro current charged cursor result source prior stopped
    refine ⟨prior.1, ?_⟩
    have last := stopped.resolve_right (by intro rejected; exact rejected prior.1)
    exact finish current charged cursor source (by omega) prior.2.2
  · exact ⟨rfl, bounded, initial⟩

/-- Global initializer traversal, using the shared source-preserving loop rule. -/
def initializerGlobalLoop {A : Type} (ops : runtime.platform.Alloc A) : InitializerModuleLoop A where
  body := fun (current, charged, cursor, result) =>
    runtime.compiler.initialize.lower_loop0.body ops current charged cursor result
  callback := runtime.compiler.initialize.lower_global ops
  length := fun module => alloc.vec.Vec.len module.env.globals
  body_eq := by
    intro current charged cursor result count size
    unfold runtime.compiler.initialize.lower_loop0.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.globals, bind_ok]
    have lengthEq : Slice.len current.module.env.globals.deref = count := by
      simpa only [Slice.len, alloc.vec.Vec.deref, alloc.vec.Vec.len, Slice.from_val] using size
    rw [lengthEq]
    cases result with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]
  callback_frame := by
    intro current next charged nextBudget cursor result _inside called
    obtain ⟨global, read, effect⟩ := runtime.compiler.initialize.lower_global.inv
      ops current next charged nextBudget cursor result called
    have same := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
    exact same

/-- Data-offset traversal, sharing the same indexed loop induction as globals. -/
def initializerDataOffsetLoop {A : Type} (ops : runtime.platform.Alloc A) : InitializerModuleLoop A where
  body := fun (current, charged, cursor, result) =>
    runtime.compiler.initialize.lower_loop2.body ops current charged cursor result
  callback := runtime.compiler.initialize.lower_data_offset ops
  length := fun module => alloc.vec.Vec.len module.tail.data
  body_eq := by
    intro current charged cursor result count size
    unfold runtime.compiler.initialize.lower_loop2.body
    simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
    rw [size]
    cases result with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]
  callback_frame := by
    intro current next charged nextBudget cursor result _inside called
    obtain ⟨segment, read, effect⟩ := runtime.compiler.initialize.lower_data_offset.inv
      ops current next charged nextBudget cursor result called
    have same := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
    exact same

/-- Element initializer traversal, using the shared source-preserving loop rule. -/
def initializerElementLoop {A : Type} (ops : runtime.platform.Alloc A) : InitializerModuleLoop A where
  body := fun (current, charged, cursor, result) =>
    runtime.compiler.initialize.lower_loop1.body ops current charged cursor result
  callback := runtime.compiler.initialize.lower_element ops
  length := fun module => alloc.vec.Vec.len module.env.elements
  body_eq := by
    intro current charged cursor result count size
    unfold runtime.compiler.initialize.lower_loop1.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
    have lengthEq : Slice.len current.module.env.elements.deref = count := by
      simpa only [Slice.len, alloc.vec.Vec.deref, alloc.vec.Vec.len, Slice.from_val] using size
    rw [lengthEq]
    cases result with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]
  callback_frame := by
    intro current next charged nextBudget cursor result inside called
    change cursor.val < current.module.env.elements.val.length at inside
    let segment := current.module.env.elements.val[cursor.val]'inside
    have found : current.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem inside
    have effect := runtime.compiler.initialize.lower_element.inv ops current next charged nextBudget cursor result called
    exact effect.source segment found

end Itasca.Compiler

end

end

/-! ## MappingConstruction -/

section

open Itasca.Representation

/-!
# Mapping Construction

Initializer loops construct module mappings while preserving the compiler and source invariants of each appended entry.
-/

/-! ## InitializerProofs -/

section

/-! The extracted synthetic-initializer emitter and constant compiler terminate
under allocator laws and representable vector lengths. Successful calls append
exactly the certified scalar/reference/vector instruction, with vector constants
embedded in the actual pool. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

@[step] theorem initializer_emit {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (fits : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () → out.2.2.val = code.val ++ [instruction] ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.emit.total ops law budget code instruction fits)
  rw [called]
  simp only [WP.spec_ok]
  intro accepted
  subst status
  exact (runtime.compiler.initialize.emit.inv ops budget afterBudget code after instruction (.Ok ()) called).success law

@[step] theorem initializer_constant {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.1 = .Ok () → ConstantLowered function out.2.2 expr ty dst ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget function expr ty dst codeFits poolFits)
  rw [called]
  simp only [WP.spec_ok]
  intro accepted
  subst status
  exact (runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr ty dst (.Ok ()) called).success law

end Itasca.Compiler

end

/-! ## InitializerExpression -/

section

/-! Successful synthetic initializer compilation retains its exact two-instruction
program, literal pool, slot width, and position in the executable module. -/

namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Actual successful expression lowering supplies the executable initializer certificate.
Source expression typing and runtime index resolution are separate obligations. -/
theorem initializer_expression {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType)
    (index : Usize) (after : runtime.compiler.ExecutableModule) (budgetAfter : runtime.compiler.Budget A)
    (success : runtime.compiler.initialize.expression ops module budget expr ty =
      .ok (.Ok index, after, budgetAfter)) :
    ∃ function, InitializerCode function expr ty ∧ index.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] := by
  exact (runtime.compiler.initialize.expression.inv ops module after budget budgetAfter expr ty (.Ok index) success).success law

end Itasca.Compiler

end

/-! ## InitializerMappings -/

section

/-! Exact retained initializer indices from the actual compiler helpers. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- A successful global initializer append records the exact source expression,
new function index, and two-instruction certificate, preserving other fields. -/
theorem initializer_lower_global {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (global : Itasca.metadata.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (success : runtime.compiler.initialize.lower_global ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function global.init global.gtype.valtype ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, global_initializers := after.global_initializers } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.global_initializers.val = module.global_initializers.val ++ [fnIndex] := by
  exact (runtime.compiler.initialize.lower_global.inv_selected ops module after budget budgetAfter
    index global found (.Ok ()) success).success law

theorem InitializerAt.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {index expr ty}
    (cert : InitializerAt before index expr ty) : InitializerAt after index expr ty := by
  obtain ⟨code, found, compiled⟩ := cert
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨code, ?_, compiled⟩
  rw [← prefixEq, List.getElem?_take] at found
  simpa [bound] using found

/-- Each successful element-value lowering appends the actual source value's
initializer and records precisely its issued function index. -/
theorem initializer_lower_element_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (success : runtime.compiler.initialize.lower_element_value ops module budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ∃ function fnIndex,
      InitializerCode function expr (Itasca.Module.Constants.referenceValueType segment.elem) ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [fnIndex] := by
  exact (runtime.compiler.initialize.lower_element_value.inv_selected ops module after budget budgetAfter
    indices outIndices i j segment expr found valueFound (.Ok ()) success).success law

theorem initializer_lower_data_active {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (memory : U32) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (active : segment.mode = .Active memory expr)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function expr .I32 ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, data_offsets := after.data_offsets } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.data_offsets.val = module.data_offsets.val ++ [some fnIndex] := by
  have effect := runtime.compiler.initialize.lower_data_offset.inv_selected ops module after budget budgetAfter
    index segment found (.Ok ()) success
  rw [active] at effect
  exact effect.active_success law

/-- Passive data segments retain an explicit absent offset without adding code. -/
theorem initializer_lower_data_passive {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (passive : segment.mode = .Passive)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    after = { module with data_offsets := after.data_offsets } ∧
      after.data_offsets.val = module.data_offsets.val ++ [none] := by
  have effect := runtime.compiler.initialize.lower_data_offset.inv_selected ops module after budget budgetAfter
    index segment found (.Ok ()) success
  rw [passive] at effect
  exact effect.passive_success law

end Itasca.Compiler

end

/-! ## InitializerMappingLoops -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem InitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expressions ty indices}
    (entries : InitializerEntries before expressions ty indices) :
    InitializerEntries after expressions ty indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

theorem GlobalInitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {globals indices}
    (entries : GlobalInitializerEntries before globals indices) :
    GlobalInitializerEntries after globals indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, global_initializers := current.global_initializers } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  GlobalInitializerEntries current.functions.val (before.module.env.globals.val.take count)
    current.global_initializers.val

theorem global_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val < before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_global ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : GlobalMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let global := before.module.env.globals.val[index.val]
  have found : current.module.env.globals.val[index.val]? = some global := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_global ops law current after budget budgetAfter index global found success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold GlobalInitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun global index => InitializerAt after.functions.val index global.init global.gtype.valtype)
        [global] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, global] using List.rel_append extended single

/-- Successful completion of the actual global initializer loop retains a
certificate for each source global, with exact module-field preservation. -/
theorem initializer_global_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_loop0 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    GlobalMappingPrefix before after before.module.env.globals.val.length := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  let P := fun next (_ : runtime.compiler.Budget A) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → cursor.val ≤ before.module.env.globals.val.length ∧ GlobalMappingPrefix before next cursor.val
  let Q := fun next (_ : runtime.compiler.Budget A) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → GlobalMappingPrefix before next before.module.env.globals.val.length
  have preserved := InitializerModuleLoop.inv
    { rules := initializerGlobalLoop ops, before := current, budget := budget, j := index, status := .Ok (),
      length := alloc.vec.Vec.len before.module.env.globals,
      lengthEq := by simpa only [initializerGlobalLoop, source], P := P, Q := Q,
      advance := (by
      intro next charged cursor same inside prior result later laterBudget nextIndex called increment accepted
      subst result
      obtain ⟨position, mapped⟩ := prior rfl
      change cursor.val < before.module.env.globals.val.length at inside
      have appended := global_mapping_append ops law before next later charged laterBudget cursor mapped inside called
      exact ⟨by omega, by simpa only [increment] using appended⟩),
      finish := (by
      intro next charged cursor result same prior stopped accepted
      obtain ⟨position, mapped⟩ := prior accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      have equal : cursor.val = before.module.env.globals.val.length := by
        change before.module.env.globals.val.length ≤ cursor.val at last
        omega
      simpa only [equal] using mapped), initial := fun _ => ⟨bound, prefixInv⟩ }
    after budgetAfter (.Ok ()) success
  exact preserved rfl

end Itasca.Compiler

end

/-! ## InitializerElementAppend -/

section

/-!
Element initializer mappings and append composition. ElementMappingPrefix and OffsetInitializer transport emitted element values and their source offset.
-/

/-! ## Initializer Element Mappings -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

def ElementMappingPrefix (before current : runtime.compiler.ExecutableModule)
    (segment : Itasca.metadata.Element) (count : Nat) (indices : alloc.vec.Vec Usize) : Prop :=
  current = { before with functions := current.functions } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  InitializerEntries current.functions.val (segment.init.val.take count)
    (Itasca.Module.Constants.referenceValueType segment.elem) indices.val

theorem element_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val < segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_value ops current budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ElementMappingPrefix before after segment (j.val + 1) outIndices := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let expr := segment.init.val[j.val]
  have exprFound : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_element_value ops law current after budget budgetAfter indices outIndices i j
      segment expr (by simpa [source] using found) exprFound success
  have extended := entries.extend (after := after.functions.val) (by simp [functions])
  refine ⟨?_, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · rw [functions, List.take_append_of_le_length]
    · exact prefixEq
    · have hlen := congrArg List.length prefixEq
      simp only [List.length_take] at hlen
      change before.functions.val.length ≤ current.functions.val.length
      omega
  · unfold InitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun expr index => InitializerAt after.functions.val index expr
          (Itasca.Module.Constants.referenceValueType segment.elem)) [expr] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, expr] using List.rel_append extended single

/-- Successful evaluation of the actual inner compiler loop establishes the
complete vector of element-value initializer certificates. -/
theorem initializer_element_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val ≤ segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_loop ops current budget i indices j (.Ok ()) =
      .ok (after, budgetAfter, outIndices, .Ok ())) :
    ElementMappingPrefix before after segment segment.init.val.length outIndices := by
  have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) prefixInv.1
  have currentFound : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
  let P := fun next (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ElementMappingPrefix before next segment cursor.val scratch
  let Q := fun next (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (result : core.result.Result Unit Itasca.error.VisitError) =>
    result = .Ok () → ElementMappingPrefix before next segment segment.init.val.length scratch
  have completed : Q after budgetAfter outIndices (.Ok ()) := by
    apply runtime.compiler.initialize.lower_element_loop.inv
      { ops := ops, before := current, budget := budget, indices := indices, i := i, j := j,
        status := .Ok (), segment := segment, found := currentFound, bounded := bound,
        P := P, Q := Q, advance := ?_, finish := ?_, initial := fun _ => prefixInv }
      after budgetAfter outIndices (.Ok ()) success
    · intro next charged scratch cursor source inside prior result last lastBudget lastIndices nextIndex lowered increment
      intro accepted
      subst result
      have appended := element_mapping_append ops law before next last charged lastBudget scratch lastIndices
        i cursor segment found (prior rfl) inside lowered
      simpa only [increment] using appended
    · intro next charged scratch cursor result source position prior stopped accepted
      have last := stopped.resolve_right (by intro rejected; exact rejected accepted)
      simpa only [last] using prior accepted
  exact completed rfl

end Itasca.Compiler

end

/-! ## Initializer Element Append -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std

theorem OffsetInitializer.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expr index}
    (cert : OffsetInitializer before expr index) : OffsetInitializer after expr index := by
  cases expr <;> cases index <;> simp only [OffsetInitializer] at cert ⊢
  exact cert.extend prefixEq

theorem initializer_lower_element {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (success : runtime.compiler.initialize.lower_element ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ indices offset,
      after = { module with functions := after.functions, element_initializers := after.element_initializers, element_offsets := after.element_offsets } ∧
      after.functions.val.take module.functions.length = module.functions.val ∧
      after.element_initializers.val = module.element_initializers.val ++ [indices] ∧
      after.element_offsets.val = module.element_offsets.val ++ [offset] ∧
      InitializerEntries after.functions.val segment.init.val
        (Itasca.Module.Constants.referenceValueType segment.elem) indices.val ∧
      OffsetInitializer after.functions.val (sourceElementOffset segment) offset := by
  have collected (stages : InitializerElementPrefix ops module budget index) :
      ElementMappingPrefix module stages.middle segment segment.init.val.length stages.indices := by
    apply initializer_element_loop ops law module module stages.middle budget stages.collected
      (alloc.vec.Vec.new Usize) stages.indices index 0#usize segment found ?_ (by change 0 ≤ segment.init.val.length; omega) stages.loopCalled
    exact ⟨rfl, by simp only [alloc.vec.Vec.length, List.take_length], .nil⟩
  have effect := runtime.compiler.initialize.lower_element.inv ops module after budget budgetAfter index (.Ok ()) success
  cases effect with
  | absent stages _status _charged offsets read pushed =>
    obtain ⟨changed, prefixEq, entries⟩ := collected stages
    simp only [List.take_length] at entries
    obtain ⟨_, rowsEq⟩ := budget_push_success ops law stages.collected stages.charged
      stages.middle.element_initializers stages.rows stages.indices stages.rowCalled
    obtain ⟨_, offsetsEq⟩ := budget_push_success ops law stages.charged budgetAfter
      stages.middle.element_offsets offsets none pushed
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) changed
    have oldRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) changed
    have oldOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) changed
    dsimp only at source oldRows oldOffsets
    rw [source, element_offset_found _ _ segment found] at read
    have offsetEq := Result.ok_injective read
    refine ⟨stages.indices, none, ?_, prefixEq, ?_, ?_, entries, ?_⟩
    · dsimp only [InitializerElementPrefix.result]
      rw [changed]
    · simpa only [InitializerElementPrefix.result, oldRows] using rowsEq
    · simpa only [oldOffsets] using offsetsEq
    · simp only [OffsetInitializer, offsetEq]
  | present stages expr final expressionBudget fnIndex _status _charged offsets read expression pushed =>
    obtain ⟨changed, prefixEq, entries⟩ := collected stages
    simp only [List.take_length] at entries
    obtain ⟨_, rowsEq⟩ := budget_push_success ops law stages.collected stages.charged
      stages.middle.element_initializers stages.rows stages.indices stages.rowCalled
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) changed
    have oldRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) changed
    have oldOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) changed
    dsimp only at source oldRows oldOffsets
    rw [source, element_offset_found _ _ segment found] at read
    have offsetEq := Result.ok_injective read
    obtain ⟨function, certificate, position, finalEq, functions⟩ :=
      initializer_expression ops law stages.result stages.charged expr .I32 fnIndex final expressionBudget expression
    obtain ⟨_, offsetsEq⟩ := budget_push_success ops law expressionBudget budgetAfter final.element_offsets offsets (some fnIndex) pushed
    have finalRows := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_initializers) finalEq
    have finalOffsets := congrArg (fun m : runtime.compiler.ExecutableModule => m.element_offsets) finalEq
    dsimp only [InitializerElementPrefix.result] at finalRows finalOffsets functions position
    have extended := entries.extend (after := final.functions.val) (by simp only [functions, List.take_left])
    refine ⟨stages.indices, some fnIndex, ?_, ?_, ?_, ?_, extended, ?_⟩
    · rw [finalEq]
      dsimp only [InitializerElementPrefix.result]
      conv_lhs => rw [changed]
    · rw [functions, List.take_append_of_le_length]
      · exact prefixEq
      · have size := congrArg List.length prefixEq
        simp only [List.length_take] at size
        change module.functions.val.length ≤ stages.middle.functions.val.length
        omega
    · simpa only [finalRows, oldRows] using rowsEq
    · simpa only [finalOffsets, oldOffsets] using offsetsEq
    · simp only [OffsetInitializer, offsetEq]
      refine ⟨function, ?_, certificate⟩
      rw [functions, position]
      simp only [alloc.vec.Vec.len, List.getElem?_concat_length]

end Itasca.Compiler

end

end

end

/-! ## SegmentEmissionContracts -/

section

open Itasca.Representation

/-! Segment-emission contracts: exact successful programs, total growth bounds,
and availability from source typing and independent allocation demand. -/
namespace Itasca.Compiler
open Aeneas Aeneas.Std

/-- Successful emission determines the appended instruction without a separate
capacity premise: the actual checked vector append supplies that bound. -/
theorem initializer_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (success : runtime.compiler.initialize.emit ops budget before instruction = .ok (.Ok (), afterBudget, after)) :
    after.val = before.val ++ [instruction] := by
  exact (runtime.compiler.initialize.emit.inv ops budget afterBudget before after instruction (.Ok ()) success).success law

/-- Integer offsets have a single instruction and no literal-pool allocation. -/
theorem initializer_offset_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (offset : (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index))
    (success : runtime.compiler.initialize.constant ops budget before expr .I32 0#u32 =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instruction, after = {before with code := after.code} ∧
      after.code.val = before.code.val ++ [instruction] ∧
      ConstantInstruction after 0#u32 expr .I32 instruction := by
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget before after expr .I32 0#u32 (.Ok ()) success
  have nonvector : ∀ lo hi, expr ≠ .V128 lo hi := by
    rcases offset with ⟨bits, rfl⟩ | ⟨index, rfl⟩ <;> intros lo hi impossible <;> cases impossible
  have poolEq := effect.pool_of_nonvector nonvector
  obtain ⟨code, pool, instruction, rfl, appended, certified⟩ := effect.success law
  change pool = before.v128_pool at poolEq
  subst pool
  exact ⟨instruction, rfl, appended, certified⟩

theorem valid_offset_shape {env : Itasca.metadata.Env} {expr : Itasca.wasm_types.ConstExpr}
    (valid : Itasca.Module.Constants.Valid env expr .I32) :
    (∃ bits, expr = .I32 bits) ∨ (∃ index, expr = .GlobalGet index) := by
  cases expr with
  | I32 bits => exact .inl ⟨bits, rfl⟩
  | GlobalGet index => exact .inr ⟨index, rfl⟩
  | I64 _ | F32 _ | F64 _ | V128 _ _ | RefFunc _ => cases valid
  | RefNull ty => cases ty <;> cases valid

/-- Source-typed i32 offsets compile with one instruction and no pool reserve.
The exact field effect is available before any publication checker runs. -/
theorem initializer_offset_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (env : Itasca.metadata.Env) (expr : Itasca.wasm_types.ConstExpr)
    (typed : Itasca.Module.Constants.Valid env expr .I32)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (capacity : function.code.length < Usize.max) (request : function.code.length + 1 ≤ bound) :
    runtime.compiler.initialize.constant ops budget function expr .I32 0#u32 ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2 = {function with code := out.2.2.code} ∧
      ∃ instruction, out.2.2.code.val = function.code.val ++ [instruction] ∧
        ConstantInstruction out.2.2 0#u32 expr .I32 instruction ⦄ := by
  have nonvector : ∀ lo hi, expr ≠ .V128 lo hi := by
    rcases valid_offset_shape typed with ⟨bits, rfl⟩ | ⟨index, rfl⟩ <;>
      intros lo hi impossible <;> cases impossible
  obtain ⟨⟨status, afterBudget, after⟩, called, accepted, used, frame, count, lowered⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.available ops bound available budget function expr .I32 0#u32
      room capacity request (fun lo hi equality => False.elim (nonvector lo hi equality)))
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr .I32 0#u32 status called
  have poolEq := effect.pool_of_nonvector nonvector
  rw [called]
  simp only [WP.spec_ok]
  obtain ⟨code, pool, instruction, rfl, appended, certified⟩ := lowered
  change pool = function.v128_pool at poolEq
  subst pool afterBudget
  exact ⟨accepted, count, rfl, rfl, instruction, appended, certified⟩

@[step] theorem initializer_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (space : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.2.2.val.length ≤ code.val.length + 1 ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.emit.total ops law budget code instruction space)
  rw [called]
  simp only [WP.spec_ok]
  have growth := (runtime.compiler.initialize.emit.inv ops budget afterBudget code after instruction status called).code law
  rcases growth with unchanged | appended
  · rw [unchanged]
    omega
  · rw [appended, List.length_append, List.length_singleton]

/-- All constant forms return normally, including an allocator or instruction
budget rejection after partial emission. Each vector grows by at most one. -/
@[step] theorem initializer_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (expr : Itasca.wasm_types.ConstExpr)
    (ty : Itasca.wasm_types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 1 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  obtain ⟨⟨status, afterBudget, after⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.constant.total ops law budget function expr ty dst codeFits poolFits)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.constant.inv ops budget afterBudget function after expr ty dst status called
  have growth := effect.growth law
  refine ⟨growth.1, growth.2, ?_⟩
  have same := congrArg (fun f : runtime.bytecode.CompiledFunction => f.indirect) effect.frame
  exact same

/-- One available instruction emission consumes one unit of instruction budget
and appends its instruction. Bounds are on actual reserve demand. -/
theorem initializer_emit_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (code : alloc.vec.Vec runtime.bytecode.Instr)
    (instruction : runtime.bytecode.Instr)
    (room : budget.instructions.val < budget.limits.max_instructions.val)
    (fits : code.length < Usize.max) (request : code.length + 1 ≤ bound) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.1 = .Ok () ∧ out.2.1.instructions.val = budget.instructions.val + 1 ∧
      out.2.1.limits = budget.limits ∧ out.2.2.val = code.val ++ [instruction] ⦄ := by
  apply WP.spec_mono (runtime.compiler.initialize.emit.available ops bound available budget code instruction room fits request)
  rintro ⟨status, afterBudget, after⟩ ⟨accepted, used, rfl, count, appended⟩
  exact ⟨accepted, count, rfl, appended⟩

theorem _root_.Itasca.runtime.compiler.initialize.emit_data.inv {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (valid : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_data ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, DataProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count} ∧
      (instructions = [] ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_data at success
  simp only [runtime.compiler.ExecutableModule.tail.eq,
    Itasca.metadata.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, .inl ⟨rfl, rfl⟩⟩
  | Active memory offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid memory offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok word =>
              have indexSpec := bounded_index index
              rw [boundedIndex, WP.spec_ok] at indexSpec
              have encoded := indexSpec word rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨⟨result, b4, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok unitValue =>
                cases unitValue
                have code3 := initializer_emit_success ops law b3 b4 third fourth _ emit3
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b5, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have code4 := initializer_emit_success ops law b4 b5 fourth fifth _ emit4
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  have output := Result.ok_injective rest
                  have fields := congrArg (fun out => out.2.2) output
                  dsimp only at fields
                  subst after
                  refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                    .MemoryInit 0#u32 word, .DataDrop word], ?_, ?_, ?_, ?_⟩
                  · exact .active memory offset mode word length encoded count instruction (firstInstruction.change_code rfl)
                  · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                  · rw [firstFields]
                  · exact .inr ⟨rfl, by rw [firstFields]⟩

theorem _root_.Itasca.runtime.compiler.initialize.emit_element.inv {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (before after : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Element)
    (found : module.module.env.elements.val[index.val]? = some segment)
    (valid : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.emit_element ops module budget before index =
      .ok (.Ok (), afterBudget, after)) :
    ∃ instructions, ElementProgram after index.val segment instructions ∧
      after.code.val = before.code.val ++ instructions ∧
      after = {before with code := after.code, slot_count := after.slot_count, indirect := after.indirect} ∧
      after.indirect.val.take before.indirect.length = before.indirect.val ∧
      (instructions.length ≤ 1 ∧ after.slot_count = before.slot_count ∨
        instructions.length = 5 ∧ after.slot_count = 3#u32) := by
  unfold runtime.compiler.initialize.emit_element at success
  simp only [runtime.compiler.ExecutableModule.env.eq,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  cases mode : segment.mode with
  | Passive =>
    simp only [mode] at success
    have output := Result.ok_injective success
    have same := congrArg (fun out => out.2.2) output
    dsimp only at same
    subst after
    exact ⟨[], .passive mode, by simp, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Declarative =>
    simp only [mode] at success
    obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok word =>
      have indexSpec := bounded_index index
      rw [boundedIndex, WP.spec_ok] at indexSpec
      have encoded := indexSpec word rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b1, instructions⟩, emitted, rest⟩ := initializer_bind_success rest
      have output := Result.ok_injective rest
      have resultEq := congrArg Prod.fst output
      dsimp only at resultEq
      subst result
      have fields := congrArg (fun out => out.2.2) output
      dsimp only at fields
      subst after
      have code := initializer_emit_success ops law budget b1 before.code instructions _ emitted
      exact ⟨[.ElemDrop word], .declarative mode word encoded, code, rfl, by simp, .inl ⟨by simp, rfl⟩⟩
  | Active table offset =>
    simp only [mode] at success
    obtain ⟨⟨result, b1, first⟩, constant, rest⟩ := initializer_bind_success success
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unitValue =>
      cases unitValue
      obtain ⟨instruction, firstFields, firstCode, firstInstruction⟩ :=
        initializer_offset_success ops law budget b1 {before with slot_count := 3#u32} first offset
          (valid_offset_shape (valid table offset mode)) constant
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨result, b2, second⟩, emit1, rest⟩ := initializer_bind_success rest
      cases result with
      | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok unitValue =>
        cases unitValue
        have code1 := initializer_emit_success ops law b1 b2 first.code second _ emit1
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨result, boundedLen, rest⟩ := initializer_bind_success rest
        cases result with
        | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok length =>
          have countSpec := bounded_index (alloc.vec.Vec.len segment.init)
          rw [boundedLen, WP.spec_ok] at countSpec
          have count := countSpec length rfl
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
          obtain ⟨⟨result, b3, third⟩, emit2, rest⟩ := initializer_bind_success rest
          cases result with
          | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
          | Ok unitValue =>
            cases unitValue
            have code2 := initializer_emit_success ops law b2 b3 second third _ emit2
            simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
            obtain ⟨result, boundedEntry, rest⟩ := initializer_bind_success rest
            cases result with
            | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
            | Ok entry =>
              have entrySpec := bounded_index (alloc.vec.Vec.len first.indirect)
              rw [boundedEntry, WP.spec_ok] at entrySpec
              have entryEncoded := entrySpec entry rfl
              simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
              obtain ⟨result, boundedIndex, rest⟩ := initializer_bind_success rest
              cases result with
              | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
              | Ok word =>
                have indexSpec := bounded_index index
                rw [boundedIndex, WP.spec_ok] at indexSpec
                have encoded := indexSpec word rfl
                simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                obtain ⟨⟨result, b4, indirect⟩, pushed, rest⟩ := initializer_bind_success rest
                cases result with
                | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                | Ok unitValue =>
                  cases unitValue
                  have indirectValues := (budget_push_success ops law b3 b4 first.indirect indirect (word, table) pushed).2
                  simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                  obtain ⟨⟨result, b5, fourth⟩, emit3, rest⟩ := initializer_bind_success rest
                  cases result with
                  | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                  | Ok unitValue =>
                    cases unitValue
                    have code3 := initializer_emit_success ops law b4 b5 third fourth _ emit3
                    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
                    obtain ⟨⟨result, b6, fifth⟩, emit4, rest⟩ := initializer_bind_success rest
                    cases result with
                    | Err error => simp [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
                    | Ok unitValue =>
                      cases unitValue
                      have code4 := initializer_emit_success ops law b5 b6 fourth fifth _ emit4
                      have output := Result.ok_injective rest
                      have fields := congrArg (fun out => out.2.2) output
                      dsimp only at fields
                      subst after
                      refine ⟨[instruction, .Const32 1#u32 0#u32, .Const32 2#u32 length,
                        .TableInit 0#u32 entry, .ElemDrop word], ?_, ?_, ?_, ?_, ?_⟩
                      · exact .active table offset mode word length entry encoded count
                          (by simp [indirectValues, entryEncoded]) instruction (firstInstruction.change_code rfl)
                      · simp [code4, code3, code2, code1, firstCode, List.append_assoc]
                      · rw [firstFields]
                      · have same := congrArg runtime.bytecode.CompiledFunction.indirect firstFields
                        dsimp only at same
                        simp [indirectValues, same]
                      · exact .inr ⟨rfl, by rw [firstFields]⟩

theorem _root_.Itasca.runtime.compiler.initialize.emit_data.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ (status, afterBudget, after) =>
      after.code.val.length ≤ function.code.val.length + 5 ∧
      after.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      after.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
  step
  repeat' first
    | (refine WP.spec_bind (initializer_constant_total ops law _ _ _ _ _ ?_ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextFunction⟩ ⟨code, pool, pairs⟩
            dsimp only at code pool pairs
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_emit_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (bounded_index _) ?_
       rintro status encoded
       cases status)
    | simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
    | split
    | (apply WP.spec.ret
       try dsimp only
       repeat' apply And.intro
       all_goals first | assumption | rfl | scalar_tac)

theorem _root_.Itasca.runtime.compiler.initialize.emit_element.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ (status, afterBudget, after) =>
      after.code.val.length ≤ function.code.val.length + 5 ∧
      after.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      after.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  step
  · simpa [alloc.vec.Vec.deref] using bound
  repeat' first
    | (refine WP.spec_bind (initializer_constant_total ops law _ _ _ _ _ ?_ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextFunction⟩ ⟨code, pool, pairs⟩
            dsimp only at code pool pairs
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_emit_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (initializer_push_total ops law _ _ _ ?_) ?_
       all_goals first
         | (rintro ⟨status, nextBudget, nextVector⟩ growth
            dsimp only at growth
            cases status)
         | scalar_tac)
    | (refine WP.spec_bind (bounded_index _) ?_
       rintro status encoded
       cases status)
    | simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from, bind_ok, bind_tc_ok]
    | split
    | (apply WP.spec.ret
       try dsimp only
       repeat' apply And.intro
       all_goals first | assumption | rfl | scalar_tac)

structure DataEmissionDemand {A : Type} (bound : Nat)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Data) : Prop where
  lookup : module.module.tail.data.val[index.val]? = some segment
  typed : ∀ memory offset, segment.mode = .Active memory offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val
  capacity : function.code.length + 5 ≤ Usize.max
  request : function.code.length + 5 ≤ bound
  indexBound : index.val ≤ U32.max
  lengthBound : segment.init.length ≤ U32.max

theorem _root_.Itasca.runtime.compiler.initialize.emit_data.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Data)
    (demand : DataEmissionDemand bound module budget function index segment) :
    runtime.compiler.initialize.emit_data ops module budget function index ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ afterBudget.instructions.val ≤ budget.instructions.val + 5 ∧
      afterBudget.limits = budget.limits ∧ after.code.length ≤ function.code.length + 5 ∧
      after.v128_pool = function.v128_pool ∧ after.indirect = function.indirect ⦄ := by
  obtain ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound⟩ := demand
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail.eq,Itasca.metadata.Module.impl.tail,bind_ok]
  rw [initializer_vec_index _ _ segment lookup,bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨rfl,by omega,rfl,by omega,rfl,rfl⟩
  | Active memory offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed memory offset mode) (by omega)
      (by change function.code.length < Usize.max; omega)
      (by change function.code.length+1 ≤ bound; omega)
      as ⟨status,b1,first,accepted,used1,limits1,fields,instruction,code1,constant⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstLength : first.code.length = function.code.length + 1 := by
      simp only [alloc.vec.Vec.length,code1,List.length_append,List.length_singleton]
    step with initializer_emit_available ops bound available b1 first.code (.Const32 1#u32 0#u32)
      (by rw [limits1]; omega) (by omega) (by omega)
      as ⟨status,b2,second,accepted,used2,limits2,code2⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available (alloc.vec.Vec.len segment.init) lengthBound
      as ⟨status,length,accepted,encodedLength⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have secondLength : second.length = function.code.length + 2 := by
      simp only [alloc.vec.Vec.length,code2,List.length_append,List.length_singleton] at firstLength ⊢
      omega
    step with initializer_emit_available ops bound available b2 second (.Const32 2#u32 length)
      (by rw [limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b3,third,accepted,used3,limits3,code3⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with initializer_emit_available ops bound available b3 third (.MemoryInit 0#u32 word)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.DataDrop word)
      (by rw [limits4,limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b5,fifth,accepted,used5,limits5,code5⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    refine ⟨rfl,?_,?_,?_,?_,?_⟩
    · omega
    · exact limits5.trans (limits4.trans (limits3.trans (limits2.trans limits1)))
    · simp only [alloc.vec.Vec.length,code5,List.length_append,List.length_singleton]
      simp only [alloc.vec.Vec.length] at fourthLength capacity
      omega
    · exact congrArg (fun value => value.v128_pool) fields
    · exact congrArg (fun value => value.indirect) fields

structure ElementEmissionDemand {A : Type} (bound : Nat)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (segment : Itasca.metadata.Element) : Prop where
  lookup : module.module.env.elements.val[index.val]? = some segment
  typed : ∀ table offset, segment.mode = .Active table offset →
      Itasca.Module.Constants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 5 ≤ budget.limits.max_instructions.val
  capacity : function.code.length + 5 ≤ Usize.max
  request : function.code.length + 5 ≤ bound
  indexBound : index.val ≤ U32.max
  lengthBound : segment.init.length ≤ U32.max
  pairIndex : function.indirect.length ≤ U32.max
  pairCapacity : function.indirect.length < Usize.max
  pairReserve : function.indirect.length + 1 ≤ bound

theorem _root_.Itasca.runtime.compiler.initialize.emit_element.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (index : Usize) (segment : Itasca.metadata.Element)
    (demand : ElementEmissionDemand bound module budget function index segment) :
    runtime.compiler.initialize.emit_element ops module budget function index ⦃ (status, afterBudget, after) =>
      status = .Ok () ∧ afterBudget.instructions.val ≤ budget.instructions.val + 5 ∧
      afterBudget.limits = budget.limits ∧ after.code.length ≤ function.code.length + 5 ∧
      after.v128_pool = function.v128_pool ∧ after.indirect.length ≤ function.indirect.length + 1 ⦄ := by
  obtain ⟨lookup, typed, instructions, capacity, request, indexBound, lengthBound, pairIndex, pairCapacity, pairReserve⟩ := demand
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env,Itasca.metadata.Env.impl.elements,bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using lookup),bind_ok]
  cases mode : segment.mode with
  | Passive =>
    simp only [mode,WP.spec_ok]
    exact ⟨rfl,by omega,rfl,by omega,rfl,by omega⟩
  | Declarative =>
    simp only [mode]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available budget function.code (.ElemDrop word)
      (by omega) (by omega) (by omega)
      as ⟨status,charged,code,accepted,used,limits,appended⟩
    refine ⟨accepted,by omega,limits,?_,?_⟩
    · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
      omega
    · omega
  | Active table offset =>
    simp only [mode]
    step with initializer_offset_available ops bound available budget {function with slot_count := 3#u32}
      module.module.env offset (typed table offset mode) (by omega)
      (by change function.code.length < Usize.max; omega)
      (by change function.code.length+1 ≤ bound; omega)
      as ⟨status,b1,first,accepted,used1,limits1,fields,instruction,code1,constant⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstLength : first.code.length = function.code.length + 1 := by
      simp only [alloc.vec.Vec.length,code1,List.length_append,List.length_singleton]
    step with initializer_emit_available ops bound available b1 first.code (.Const32 1#u32 0#u32)
      (by rw [limits1]; omega) (by omega) (by omega)
      as ⟨status,b2,second,accepted,used2,limits2,code2⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available (alloc.vec.Vec.len segment.init) lengthBound
      as ⟨status,length,accepted,encodedLength⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have secondLength : second.length = function.code.length + 2 := by
      simp only [alloc.vec.Vec.length,code2,List.length_append,List.length_singleton] at firstLength ⊢
      omega
    step with initializer_emit_available ops bound available b2 second (.Const32 2#u32 length)
      (by rw [limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b3,third,accepted,used3,limits3,code3⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have firstPairs : first.indirect = function.indirect := congrArg (fun value => value.indirect) fields
    step with bounded_index_available (alloc.vec.Vec.len first.indirect) (by simpa [firstPairs] using pairIndex)
      as ⟨status,entry,accepted,entryEq⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with bounded_index_available index indexBound as ⟨status,word,accepted,encoded⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have thirdLength : third.length = function.code.length + 3 := by
      simp only [alloc.vec.Vec.length,code3,List.length_append,List.length_singleton] at secondLength ⊢
      omega
    step with budget_push_available ops bound available b3 first.indirect (word,table)
      (by simpa [firstPairs] using pairCapacity) (by simpa [firstPairs] using pairReserve)
      as ⟨status,pairBudget,pairs,accepted,sameBudget,appendedPairs⟩
    subst status pairBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    step with initializer_emit_available ops bound available b3 third (.TableInit 0#u32 entry)
      (by rw [limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b4,fourth,accepted,used4,limits4,code4⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have fourthLength : fourth.length = function.code.length + 4 := by
      simp only [alloc.vec.Vec.length,code4,List.length_append,List.length_singleton] at thirdLength ⊢
      omega
    step with initializer_emit_available ops bound available b4 fourth (.ElemDrop word)
      (by rw [limits4,limits3,limits2,limits1]; omega) (by omega) (by omega)
      as ⟨status,b5,fifth,accepted,used5,limits5,code5⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    refine ⟨trivial,?_,?_,?_,?_,?_⟩
    · omega
    · exact limits5.trans (limits4.trans (limits3.trans (limits2.trans limits1)))
    · simp only [alloc.vec.Vec.length,code5,List.length_append,List.length_singleton]
      simp only [alloc.vec.Vec.length] at fourthLength capacity
      omega
    · exact congrArg (fun value => value.v128_pool) fields
    · simp only [alloc.vec.Vec.length,appendedPairs,List.length_append,List.length_singleton]
      simp [firstPairs]

end Itasca.Compiler

end
