import Exec.Code.Local.Initializer.InitializerElementAppend

namespace Exec.Code
open Aeneas Aeneas.Std

def ElementValueMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.module.Element) (rows : List (alloc.vec.Vec Usize)) : Prop :=
  List.Forall₂ (fun segment indices => InitializerEntries functions segment.init.val
    (Itasca.ModuleConstants.referenceValueType segment.elem) indices.val) segments rows

def ElementOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.module.Element) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceElementOffset segment) offset)
    segments offsets

theorem ElementValueMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments rows}
    (entries : ElementValueMappings before segments rows) :
    ElementValueMappings after segments rows := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

theorem ElementOffsetMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments offsets}
    (entries : ElementOffsetMappings before segments offsets) :
    ElementOffsetMappings after segments offsets := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def ElementModulePrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, element_initializers := current.element_initializers, element_offsets := current.element_offsets } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  ElementValueMappings current.functions.val (before.module.env.elements.val.take count) current.element_initializers.val ∧
  ElementOffsetMappings current.functions.val (before.module.env.elements.val.take count) current.element_offsets.val

theorem initializer_prefix_trans {T : Type} {before middle after : List T}
    (first : middle.take before.length = before) (second : after.take middle.length = middle) :
    after.take before.length = before := by
  have length := congrArg List.length first
  simp only [List.length_take] at length
  have bound : before.length ≤ middle.length := by omega
  rw [← second, List.take_take, Nat.min_eq_left bound] at first
  exact first

theorem element_module_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementModulePrefix before current index.val)
    (bound : index.val < before.module.env.elements.val.length)
    (success : runtime.compiler.initialize.lower_element ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : ElementModulePrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries, offsets⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let segment := before.module.env.elements.val[index.val]
  have found : current.module.env.elements.val[index.val]? = some segment := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨row, offset, changed, functions, rows, offsetList, valuesCert, offsetCert⟩ :=
    initializer_lower_element ops law current after budget budgetAfter index segment found success
  have extended := entries.extend functions
  have extendedOffsets := offsets.extend functions
  refine ⟨?_, initializer_prefix_trans prefixEq functions, ?_, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · unfold ElementValueMappings at extended ⊢
    rw [List.take_add_one, rows]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extended (.cons valuesCert .nil)
  · unfold ElementOffsetMappings at extendedOffsets ⊢
    rw [List.take_add_one, offsetList]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extendedOffsets (.cons offsetCert .nil)

theorem initializer_elements_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : ElementModulePrefix before current index.val)
    (bound : index.val ≤ before.module.env.elements.val.length)
    (success : runtime.compiler.initialize.lower_loop1 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    ElementModulePrefix before after before.module.env.elements.val.length := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.env.elements.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.env.elements.val.length ∧
      ElementModulePrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → ElementModulePrefix before p.1 before.module.env.elements.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop1.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop1.body at body
    simp only [runtime.compiler.ExecutableModule.env, Exec.module.Module.env,
      Itasca.module.Module.impl.env, Exec.module.Env.elements, Itasca.module.Env.impl.elements, bind_ok] at body
    cases status with
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte] at body
      split at body <;> (have hf := Result.ok_injective body; subst flow; simp [post])
    | Ok unit =>
      cases unit
      obtain ⟨hi, prefixInv⟩ := hinv rfl
      have source := congrArg runtime.compiler.ExecutableModule.module prefixInv.1
      dsimp only at source
      rw [source] at body
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte] at body
      split at body
      · rename_i more
        have hmore : i.val < before.module.env.elements.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.env.elements.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := element_module_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.env.elements.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop1.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

end Exec.Code
