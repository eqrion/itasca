import Exec.Code.Module.InitializerTotalElement
namespace Itasca.Runtime.Code
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
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.globals, bind_ok]
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
      Itasca.module.Module.impl.tail, bind_ok]
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
def initializerElementCost (elements : List Itasca.module.Element) : Nat :=
  (elements.map (fun e => e.init.val.length + 3)).sum

theorem initializer_element_cost_step (elements : List Itasca.module.Element)
    (index : Nat) (segment : Itasca.module.Element) (found : elements[index]? = some segment) :
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
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
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
end Itasca.Runtime.Code
