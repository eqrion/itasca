import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpression
import Itasca.Module.Const.Syntax

/-! Exact retained initializer indices from the actual compiler helpers. -/
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Invert an ordinary result of an extracted monadic bind. -/
theorem initializer_bind_success {T U : Type} {input : Result T} {next : T → Result U}
    {out : U} (success : (input >>= next) = .ok out) :
    ∃ value, input = .ok value ∧ next value = .ok out := by
  change Aeneas.Std.bind input next = .ok out at success
  cases input with
  | ret value => exact ⟨value, rfl, by simpa only [bind_ok] using success⟩
  | vis event continuation => simp only [bind_vis] at success; exact (vis_not_ok success).elim
  | div => simp only [bind_div] at success; exact (div_not_ok success).elim

theorem initializer_slice_index {T : Type} (values : Slice T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) : Slice.index_usize values index = .ok value := by
  have bound : index.val < values.length := (List.getElem?_eq_some_iff.mp found).1
  have spec : Slice.index_usize values index ⦃ out => out = value ⦄ := by
    step as ⟨out, hout⟩
    have read := List.getElem?_eq_getElem bound
    rw [found] at read
    exact hout.trans (Option.some.inj read).symm
  obtain ⟨out, call, rfl⟩ := WP.spec_imp_exists spec
  exact call

/-- A successful global initializer append records the exact source expression,
new function index, and two-instruction certificate, preserving other fields. -/
theorem initializer_lower_global {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (global : Itasca.module.Global)
    (found : module.module.env.globals.val[index.val]? = some global)
    (success : runtime.compiler.initialize.lower_global ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ function fnIndex,
      InitializerCode function global.init global.gtype.valtype ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions, global_initializers := after.global_initializers } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      after.global_initializers.val = module.global_initializers.val ++ [fnIndex] := by
  unfold runtime.compiler.initialize.lower_global at success
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.globals, bind_ok] at success
  rw [initializer_slice_index _ _ global (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget global.init global.gtype.valtype fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, indices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    dsimp only at fields
    subst after
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 middle.global_initializers indices fnIndex pushed
    refine ⟨function, fnIndex, certificate, position, ?_, appended, ?_⟩
    · rw [changed]
    · have same := congrArg runtime.compiler.ExecutableModule.global_initializers changed
      change middle.global_initializers = module.global_initializers at same
      simpa only [same] using pushedValues

def InitializerAt (functions : List runtime.bytecode.CompiledFunction)
    (index : Usize) (expr : Itasca.types.ConstExpr) (ty : Itasca.types.ValueType) : Prop :=
  ∃ code, functions[index.val]? = some code ∧ InitializerCode code expr ty

theorem InitializerAt.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {index expr ty}
    (cert : InitializerAt before index expr ty) : InitializerAt after index expr ty := by
  obtain ⟨code, found, compiled⟩ := cert
  have bound := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨code, ?_, compiled⟩
  rw [← prefixEq, List.getElem?_take] at found
  simpa [bound] using found

theorem initializer_vec_index {T : Type} (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (found : values.val[index.val]? = some value) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T) values index = .ok value :=
  initializer_slice_index values.slice index value found

/-- Each successful element-value lowering appends the actual source value's
initializer and records precisely its issued function index. -/
theorem initializer_lower_element_value {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.module.Element) (expr : Itasca.types.ConstExpr)
    (found : module.module.env.elements.val[i.val]? = some segment)
    (valueFound : segment.init.val[j.val]? = some expr)
    (success : runtime.compiler.initialize.lower_element_value ops module budget indices i j =
      .ok (.Ok (), after, budgetAfter, outIndices)) :
    ∃ function fnIndex,
      InitializerCode function expr (Itasca.ModuleConstants.referenceValueType segment.elem) ∧
      fnIndex.val = module.functions.val.length ∧
      after = { module with functions := after.functions } ∧
      after.functions.val = module.functions.val ++ [function] ∧
      outIndices.val = indices.val ++ [fnIndex] := by
  unfold runtime.compiler.initialize.lower_element_value at success
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok] at success
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok,
    initializer_vec_index _ _ expr valueFound, bind_ok] at success
  simp only [bind_ok] at success
  have elemType : types.ElemType.value_type segment.elem =
      .ok (Itasca.ModuleConstants.referenceValueType segment.elem) := by
    cases segment.elem <;> rfl
  rw [elemType, bind_ok] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget expr _ fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, outputIndices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    have sameIndices := congrArg (fun out => out.2.2.2) output
    dsimp only at fields sameIndices
    subst after outIndices
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 indices outputIndices fnIndex pushed
    exact ⟨function, fnIndex, certificate, position, changed, appended, pushedValues⟩

theorem initializer_lower_data_active {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.module.Data)
    (memory : U32) (expr : Itasca.types.ConstExpr)
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
  unfold runtime.compiler.initialize.lower_data_offset at success
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok, active] at success
  obtain ⟨⟨result, middle, b1⟩, expression, rest⟩ := initializer_bind_success success
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok fnIndex =>
    obtain ⟨function, certificate, position, changed, appended⟩ :=
      initializer_expression ops law module budget expr .I32 fnIndex middle b1 expression
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair] at rest
    obtain ⟨⟨result, b2, indices⟩, pushed, rest⟩ := initializer_bind_success rest
    have output := Result.ok_injective rest
    have sameResult := congrArg Prod.fst output
    dsimp only at sameResult
    subst result
    have fields := congrArg (fun out => out.2.1) output
    dsimp only at fields
    subst after
    obtain ⟨_, pushedValues⟩ := budget_push_success ops law b1 b2 middle.data_offsets indices (some fnIndex) pushed
    refine ⟨function, fnIndex, certificate, position, ?_, appended, ?_⟩
    · rw [changed]
    · have same := congrArg runtime.compiler.ExecutableModule.data_offsets changed
      change middle.data_offsets = module.data_offsets at same
      simpa only [same] using pushedValues

/-- Passive data segments retain an explicit absent offset without adding code. -/
theorem initializer_lower_data_passive {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.module.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (passive : segment.mode = .Passive)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    after = { module with data_offsets := after.data_offsets } ∧
      after.data_offsets.val = module.data_offsets.val ++ [none] := by
  unfold runtime.compiler.initialize.lower_data_offset at success
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok] at success
  rw [initializer_vec_index _ _ segment found, bind_ok, passive] at success
  obtain ⟨⟨result, b1, indices⟩, pushed, rest⟩ := initializer_bind_success success
  have output := Result.ok_injective rest
  have sameResult := congrArg Prod.fst output
  dsimp only at sameResult
  subst result
  have fields := congrArg (fun out => out.2.1) output
  dsimp only at fields
  subst after
  obtain ⟨_, pushedValues⟩ := budget_push_success ops law budget b1 module.data_offsets indices none pushed
  exact ⟨rfl, pushedValues⟩

end Itasca.Runtime.Code
