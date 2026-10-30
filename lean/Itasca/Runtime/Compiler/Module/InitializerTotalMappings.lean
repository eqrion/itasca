import Itasca.Runtime.Compiler.Module.InitializerTotalBasic

/-!
Normal return of element initializer values and the initializer mapping loops.
-/

/-! ## Initializer Total Element -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000

@[step] theorem initializer_element_value_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (bound : j.val < segment.init.val.length) (capacity : indices.val.length < Usize.max)
    (space : initializerSize m + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element_value ops m budget indices i j ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 1 ∧
      out.2.2.2.val.length ≤ indices.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.lower_element_value
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  step as ⟨expr, read⟩
  try simp only [bind_ok]
  have tyEq : wasm_types.ElemType.value_type segment.elem =
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
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.metadata.Element)
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
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
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
        runtime.compiler.ExecutableModule.env,
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
end Itasca.Runtime.Compiler

end

/-! ## Initializer Total Mappings -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000

@[step] theorem initializer_mapping_loop0_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop0
  apply loop.spec_decr_nat (fun st => m.module.env.globals.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + 2 * (m.module.env.globals.val.length - st.2.2.1.val) ≤
        initializerSize m + 2 * (m.module.env.globals.val.length - i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop0.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.globals, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.env.globals.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.env.globals.val.length := by simpa [same] using inbounds
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_global_total ops law current b index inbounds (by omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        exact ⟨source.trans same, by scalar_tac, by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩

@[step] theorem initializer_mapping_loop2_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop2
  apply loop.spec_decr_nat (fun st => m.module.tail.data.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + 2 * (m.module.tail.data.val.length - st.2.2.1.val) ≤
        initializerSize m + 2 * (m.module.tail.data.val.length - i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop2.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.metadata.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.tail.data.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.tail.data.val.length := by simpa [same] using inbounds
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_data_offset_total ops law current b index inbounds (by omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        exact ⟨source.trans same, by scalar_tac, by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩

/-- Exact remaining append allowance for element initializer rows and offsets. -/
def initializerElementCost (elements : List Itasca.metadata.Element) : Nat :=
  (elements.map (fun e => e.init.val.length + 3)).sum

theorem initializer_element_cost_step (elements : List Itasca.metadata.Element)
    (index : Nat) (segment : Itasca.metadata.Element) (found : elements[index]? = some segment) :
    initializerElementCost (elements.drop index) = segment.init.val.length + 3 +
      initializerElementCost (elements.drop (index + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp found).1]
  have element := (List.getElem?_eq_some_iff.mp found).2
  simp [initializerElementCost, element]

@[step] theorem initializer_mapping_loop1_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop1
  apply loop.spec_decr_nat (fun st => m.module.env.elements.val.length - st.2.2.1.val)
    (fun st => st.1.module = m.module ∧
      initializerSize st.1 + initializerElementCost (m.module.env.elements.val.drop st.2.2.1.val) ≤
        initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val))
  · rintro ⟨current, b, index, result⟩ ⟨same, size⟩
    unfold runtime.compiler.initialize.lower_loop1.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < current.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      have originalBound : index.val < m.module.env.elements.val.length := by simpa [same] using inbounds
      let segment := current.module.env.elements.val[index.val]
      have found : current.module.env.elements.val[index.val]? = some segment := List.getElem?_eq_getElem inbounds
      have originalFound : m.module.env.elements.val[index.val]? = some segment := by simpa [same] using found
      have cost := initializer_element_cost_step _ _ _ originalFound
      dsimp only [segment] at cost
      cases result with
      | Err error => simp [core.result.Result.is_ok, same]; omega
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_element_total ops law current b index segment found (by dsimp only [segment]; omega)
          as ⟨status, next, b1, source, growth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨source.trans same, ?_, ?_⟩
        · rw [increment]; omega
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨same, by omega⟩
  · exact ⟨rfl, Nat.le_refl _⟩
end Itasca.Runtime.Compiler

end
