import Itasca.Module.Const.Parser
import Itasca.Runtime.Compiler.Local.Initializer.ExpressionContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

private theorem initializer_element_type_eq (element : Itasca.wasm_types.ElemType) :
    Itasca.wasm_types.ElemType.value_type element = .ok (Itasca.ModuleConstants.referenceValueType element) := by
  cases element <;> rfl

/-- Element values compile an expression and append its index to the temporary
mapping vector, keeping both stages' normal error states. -/
inductive InitializerElementValueEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule →
    runtime.compiler.Budget A → alloc.vec.Vec Usize → Prop where
  | rejected {error middle afterBudget}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget expr ty =
        .ok (.Err error, middle, afterBudget)) :
      InitializerElementValueEffect ops before budget indices expr ty (.Err error) middle afterBudget indices
  | appended {functionIndex middle expressionBudget status afterBudget outIndices}
      (expressionCalled : runtime.compiler.initialize.expression ops before budget expr ty =
        .ok (.Ok functionIndex, middle, expressionBudget))
      (pushed : runtime.compiler.Budget.push ops expressionBudget indices functionIndex =
        .ok (status, afterBudget, outIndices)) :
      InitializerElementValueEffect ops before budget indices expr ty status middle afterBudget outIndices

theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize) (i j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_value ops before budget indices i j =
      .ok (status, after, afterBudget, outIndices)) :
    ∃ segment expr, Slice.index_usize before.module.env.elements.deref i = .ok segment ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Itasca.wasm_types.ConstExpr) segment.init j = .ok expr ∧
      InitializerElementValueEffect ops before budget indices expr (Itasca.ModuleConstants.referenceValueType segment.elem)
        status after afterBudget outIndices := by
  unfold runtime.compiler.initialize.lower_element_value at called
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env,
    Itasca.metadata.Env.impl.elements, bind_ok] at called
  obtain ⟨segment, selected, tail⟩ := bind_ok_inv _ _ _ called
  obtain ⟨expr, valueSelected, tail⟩ := bind_ok_inv _ _ _ tail
  refine ⟨segment, expr, selected, valueSelected, ?_⟩
  rw [selected, bind_ok, initializer_element_type_eq, bind_ok] at tail
  obtain ⟨⟨expressionStatus, middle, expressionBudget⟩, expressionCalled, tail⟩ := bind_ok_inv _ _ _ tail
  cases expressionStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl, rfl⟩ := tail
    exact .rejected expressionCalled
  | Ok functionIndex =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨pushedStatus, pushedBudget, pushedIndices⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl, rfl⟩ := tail
    exact .appended expressionCalled pushed

theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.inv_selected {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_value ops before budget indices i j =
      .ok (status, after, afterBudget, outIndices)) :
    InitializerElementValueEffect ops before budget indices expr (Itasca.ModuleConstants.referenceValueType segment.elem)
      status after afterBudget outIndices := by
  obtain ⟨actual, value, selected, valueSelected, effect⟩ :=
    runtime.compiler.initialize.lower_element_value.inv ops before after budget afterBudget indices outIndices i j status called
  rw [initializer_slice_index before.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)] at selected
  have same := Result.ok_injective selected
  subst actual
  rw [initializer_vec_index _ _ expr valueFound] at valueSelected
  have valueEq := Result.ok_injective valueSelected
  subst value
  exact effect

theorem InitializerElementValueEffect.frame {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty status}
    (effect : InitializerElementValueEffect ops before budget indices expr ty status after afterBudget outIndices) :
    after = {before with functions := after.functions} := by
  cases effect with
  | rejected expressionCalled => exact (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame
  | appended expressionCalled pushed => exact (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).frame

theorem InitializerElementValueEffect.growth {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty status}
    (effect : InitializerElementValueEffect ops before budget indices expr ty status after afterBudget outIndices)
    (law : Platform.AllocCorrect ops) :
    after.functions.val.length ≤ before.functions.val.length + 1 ∧ outIndices.val.length ≤ indices.val.length + 1 := by
  cases effect with
  | rejected expressionCalled =>
    exact ⟨(runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).growth law, by omega⟩
  | appended expressionCalled pushed =>
    refine ⟨(runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).growth law, ?_⟩
    have changed := budget_push_code_result ops law _ _ _ _ _ _ pushed
    rcases changed with same | appended
    · rw [same]
      omega
    · simp only [appended, List.length_append, List.length_singleton, Nat.le_refl]

theorem InitializerElementValueEffect.success {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {indices outIndices expr ty}
    (effect : InitializerElementValueEffect ops before budget indices expr ty (.Ok ()) after afterBudget outIndices)
    (law : Platform.AllocCorrect ops) :
    ∃ function functionIndex, InitializerCode function expr ty ∧ functionIndex.val = before.functions.val.length ∧
      after = {before with functions := after.functions} ∧ after.functions.val = before.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [functionIndex] := by
  cases effect with
  | appended expressionCalled pushed =>
    obtain ⟨function, certified, indexEq, frame, appended⟩ :=
      (runtime.compiler.initialize.expression.inv ops _ _ _ _ _ _ _ expressionCalled).success law
    exact ⟨function, _, certified, indexEq, frame, appended, (budget_push_success ops law _ _ _ _ _ pushed).2⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.total {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (functionsFit : module.functions.length < Usize.max) (indicesFit : indices.length < Usize.max) :
    runtime.compiler.initialize.lower_element_value ops module budget indices i j ⦃ _ => True ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env,
    Itasca.metadata.Env.impl.elements, bind_ok]
  have selected := initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)
  have valueSelected := initializer_vec_index _ _ expr valueFound
  simp only [selected, valueSelected, bind_ok, initializer_element_type_eq]
  step with runtime.compiler.initialize.expression.total ops law module budget expr _ functionsFit
    as ⟨status, middle, expressionBudget⟩
  cases status with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, WP.spec_ok]
  | Ok functionIndex =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law expressionBudget indices functionIndex indicesFit
      as ⟨status, afterBudget, outIndices, changed⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_value.available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (segment : Itasca.metadata.Element) (expr : Itasca.wasm_types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (vector : ∀ lo hi, expr = .V128 lo hi → Itasca.ModuleConstants.referenceValueType segment.elem = .V128)
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (functionsRequest : module.functions.length + 1 ≤ bound) (functionsFit : module.functions.length < Usize.max)
    (indicesRequest : indices.length + 1 ≤ bound) (indicesFit : indices.length < Usize.max) :
    runtime.compiler.initialize.lower_element_value ops module budget indices i j ⦃ (status, after, afterBudget, outIndices) =>
      status = .Ok () ∧ afterBudget.instructions.val = budget.instructions.val + 2 ∧
      afterBudget.limits = budget.limits ∧ after = {module with functions := after.functions} ∧
      outIndices.val = indices.val ++ [alloc.vec.Vec.len module.functions] ∧
      ∃ function, InitializerCode function expr (Itasca.ModuleConstants.referenceValueType segment.elem) ∧
        after.functions.val = module.functions.val ++ [function] ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Module.impl.env,
    Itasca.metadata.Env.impl.elements, bind_ok]
  have selected := initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found)
  have valueSelected := initializer_vec_index _ _ expr valueFound
  simp only [selected, valueSelected, bind_ok, initializer_element_type_eq]
  step with runtime.compiler.initialize.expression.available ops bound available module budget expr _
    vector instructions codeRequest functionsRequest functionsFit
    as ⟨status, middle, expressionBudget, accepted, count, limits, function, certified, appended, frame⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with budget_push_available ops bound available expressionBudget indices
    (alloc.vec.Vec.len module.functions) indicesFit indicesRequest
    as ⟨status, afterBudget, outIndices, accepted, budgetEq, pushed⟩
  refine ⟨accepted, ?_, ?_, frame, pushed, function, certified, appended⟩
  · rw [budgetEq]
    exact count
  · rw [budgetEq]
    exact limits

end Itasca.Runtime.Compiler
