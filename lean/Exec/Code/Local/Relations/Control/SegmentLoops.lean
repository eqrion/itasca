import Exec.Code.Local.Relations.Common.SegmentPrefix

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem element_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : ElementProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.env.elements.length)
    (valid : ∀ segment ∈ module.module.env.elements.val, ∀ table offset,
      segment.mode = .Active table offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop3 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, ElementProgramPrefix module seed after module.module.env.elements.length finalPrograms := by
  classical
  let measure := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    if state.2.2.1 = .Ok () then module.module.env.elements.length - state.2.1.val + 1 else 0
  let inv := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    state.2.2.1 = .Ok () → state.2.1.val ≤ module.module.env.elements.length ∧
      ∃ programs, ElementProgramPrefix module seed state.2.2.2 state.2.1.val programs
  let post := fun state : runtime.compiler.Budget A × core.result.Result Unit Itasca.error.VisitError ×
      runtime.bytecode.CompiledFunction =>
    state.2.1 = .Ok () → ∃ programs, ElementProgramPrefix module seed state.2.2 module.module.env.elements.length programs
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop3.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨b, i, status, function⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop3.body at body
    simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unitValue =>
      cases unitValue
      obtain ⟨hi, programs, prefixInv⟩ := hinv rfl
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < module.module.env.elements.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextBudget, nextFunction⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := module.module.env.elements.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added, WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unitValue =>
          cases unitValue
          obtain ⟨nextPrograms, nextPrefix⟩ := element_program_append ops law module seed function nextFunction
            programs b nextBudget i prefixInv hmore valid lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, nextPrograms, by simpa only [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = module.module.env.elements.length := by
          simp [alloc.vec.Vec.deref] at stopped
          simp only [alloc.vec.Vec.length] at hi ⊢
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        exact ⟨programs, by simpa only [stop] using prefixInv⟩
  have result := initializer_loop_success
    (fun state => runtime.compiler.initialize.lower_loop3.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (budget, index, .Ok (), current)
    (by exact fun _ => ⟨bound, programs, prefixInv⟩) (budgetAfter, .Ok (), after) success
  exact result rfl

/-- Actual successful segment-emission loop establishes a complete syntactic
prefix; no loop totality or runtime correctness is a premise. -/
theorem data_program_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module : runtime.compiler.ExecutableModule)
    (seed current after : runtime.bytecode.CompiledFunction)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (programs : List (List runtime.bytecode.Instr))
    (prefixInv : DataProgramPrefix module seed current index.val programs)
    (bound : index.val ≤ module.module.tail.data.length)
    (valid : ∀ segment ∈ module.module.tail.data.val, ∀ memory offset,
      segment.mode = .Active memory offset → Itasca.ModuleConstants.Valid module.module.env offset .I32)
    (success : runtime.compiler.initialize.lower_loop4 ops module budget index (.Ok ()) current =
      .ok (budgetAfter, .Ok (), after)) :
    ∃ finalPrograms, DataProgramPrefix module seed after module.module.tail.data.length finalPrograms := by
  classical
  let measure := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    if state.2.2.1 = .Ok () then module.module.tail.data.length - state.2.1.val + 1 else 0
  let inv := fun state : runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError × runtime.bytecode.CompiledFunction =>
    state.2.2.1 = .Ok () → state.2.1.val ≤ module.module.tail.data.length ∧
      ∃ programs, DataProgramPrefix module seed state.2.2.2 state.2.1.val programs
  let post := fun state : runtime.compiler.Budget A × core.result.Result Unit Itasca.error.VisitError ×
      runtime.bytecode.CompiledFunction =>
    state.2.1 = .Ok () → ∃ programs, DataProgramPrefix module seed state.2.2 module.module.tail.data.length programs
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop4.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨b, i, status, function⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop4.body at body
    simp only [runtime.compiler.ExecutableModule.tail, Exec.module.Module.tail,
      Itasca.module.Module.impl.tail, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unitValue =>
      cases unitValue
      obtain ⟨hi, programs, prefixInv⟩ := hinv rfl
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < module.module.tail.data.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextBudget, nextFunction⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := module.module.tail.data.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added, WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unitValue =>
          cases unitValue
          obtain ⟨nextPrograms, nextPrefix⟩ := data_program_append ops law module seed function nextFunction
            programs b nextBudget i prefixInv hmore valid lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, nextPrograms, by simpa only [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = module.module.tail.data.length := by
          simp [alloc.vec.Vec.deref] at stopped
          simp only [alloc.vec.Vec.length] at hi ⊢
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        exact ⟨programs, by simpa only [stop] using prefixInv⟩
  have result := initializer_loop_success
    (fun state => runtime.compiler.initialize.lower_loop4.body ops module state.1 state.2.1 state.2.2.1 state.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (budget, index, .Ok (), current)
    (by exact fun _ => ⟨bound, programs, prefixInv⟩) (budgetAfter, .Ok (), after) success
  exact result rfl

end Exec.Code
