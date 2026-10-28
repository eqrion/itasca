import Exec.Code.Module.InitializerTotalBasic
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000

@[step] theorem initializer_element_value_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.module.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val < segment.init.val.length) (capacity : indices.val.length < Usize.max)
    (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_value ops m budget indices i j ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ∧
      out.2.2.2.val.length ≤ indices.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  step as ⟨expr, read⟩
  try simp only [bind_ok]
  have tyEq : types.ElemType.value_type segment.elem =
      .ok (Itasca.ModuleConstants.referenceValueType segment.elem) := by cases segment.elem <;> rfl
  rw [tyEq, bind_ok]
  step with initializer_expression_total ops law m budget expr _ space
    as ⟨status, middle, nextBudget, same, size⟩
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same, size]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_push_total ops law nextBudget indices value capacity
      as ⟨status, finalBudget, nextIndices, count⟩
    exact ⟨same, size, count⟩

@[step] theorem initializer_element_values_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (indices : alloc.vec.Vec Usize) (j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.module.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val ≤ segment.init.val.length) (indicesBound : indices.val.length ≤ j.val)
    (space : initializerSize m + (segment.init.val.length - j.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_loop ops m budget i indices j status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + (segment.init.val.length - j.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_element_loop
  apply loop.spec_decr_nat (fun st => segment.init.val.length - st.2.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + (segment.init.val.length - st.2.2.2.1.val) ≤
        initializerSize m + (segment.init.val.length - j.val) ∧
      st.2.2.1.val.length ≤ st.2.2.2.1.val ∧ st.2.2.2.1.val ≤ segment.init.val.length)
  · rintro ⟨current, b, ix, position, result⟩ ⟨same, size, ixBound, positionBound⟩
    unfold runtime.compiler.initialize.lower_element_loop.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
    rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref, same] using found), bind_ok]
    split
    · rename_i more
      have posLt : position.val < segment.init.val.length := by scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_element_value_total ops law current b ix i position segment
          (by simpa [same] using found) posLt
          (by have := segment.init.property; omega) (by omega)
          as ⟨status, next, b1, ix1, source, growth, indexGrowth⟩
        step as ⟨nextPosition, increment⟩
        refine ⟨source.trans same, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _, indicesBound, bound⟩

@[step] theorem initializer_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.module.Element)
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
        runtime.compiler.ExecutableModule.env,
        Itasca.module.Module.impl.env, runtime.compiler.initialize.element_offset, Itasca.module.Env.impl.elements]
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
end Itasca.Runtime.Code
