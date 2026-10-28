import Exec.Code.Local.Initializer.InitializerMappingLoops

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def ElementMappingPrefix (before current : runtime.compiler.ExecutableModule)
    (segment : Itasca.module.Element) (count : Nat) (indices : alloc.vec.Vec Usize) : Prop :=
  current = { before with functions := current.functions } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  InitializerEntries current.functions.val (segment.init.val.take count)
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val

theorem element_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (segment : Itasca.module.Element)
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
          (Itasca.ModuleConstants.referenceValueType segment.elem)) [expr] [fnIndex] := by
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
    (i j : Usize) (segment : Itasca.module.Element)
    (found : before.module.env.elements.val[i.val]? = some segment)
    (prefixInv : ElementMappingPrefix before current segment j.val indices)
    (bound : j.val ≤ segment.init.val.length)
    (success : runtime.compiler.initialize.lower_element_loop ops current budget i indices j (.Ok ()) =
      .ok (after, budgetAfter, outIndices, .Ok ())) :
    ElementMappingPrefix before after segment segment.init.val.length outIndices := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2.2 = .Ok () then segment.init.val.length - p.2.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2.2 = .Ok () → p.2.2.2.1.val ≤ segment.init.val.length ∧
      ElementMappingPrefix before p.1 segment p.2.2.2.1.val p.2.2.1
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      alloc.vec.Vec Usize × core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → ElementMappingPrefix before p.1 segment segment.init.val.length p.2.2.1
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_element_loop.body ops i state.1 state.2.1
        state.2.2.1 state.2.2.2.1 state.2.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, values, k, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_element_loop.body at body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      obtain ⟨actualSegment, indexed, rest⟩ := initializer_bind_success body
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at rest
      split at rest <;> (have hf := Result.ok_injective rest; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hk, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source, initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : k.val < segment.init.val.length := by simpa using more
        obtain ⟨⟨result, nextModule, nextBudget, nextValues⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : k + 1#usize ⦃ next => next.val = k.val + 1 ⦄ := by
          have size := segment.init.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := element_mapping_append ops law before module nextModule b nextBudget
            values nextValues i k segment found prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : k.val = segment.init.val.length := by simp at stopped; omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_element_loop.body ops i p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow)
    (current, budget, indices, j, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, outIndices, .Ok ()) success
  exact result rfl

end Itasca.Runtime.Code
