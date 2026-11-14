import Itasca.Runtime.Compiler.Local.Initializer.ElementValueContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

private abbrev ElementInitializerState (A : Type) := runtime.compiler.ExecutableModule ×
  runtime.compiler.Budget A × alloc.vec.Vec Usize × Usize × core.result.Result Unit Itasca.error.VisitError

private theorem element_loop_body_eq {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (i j : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (segment : Itasca.metadata.Element) (found : module.module.env.elements.val[i.val]? = some segment) :
    runtime.compiler.initialize.lower_element_loop.body ops i module budget indices j status =
      if j < alloc.vec.Vec.len segment.init then
        match status with
        | .Err _ => .ok (.done (module, budget, indices, status))
        | .Ok () => do
          let (result, next, nextBudget, nextIndices) ← runtime.compiler.initialize.lower_element_value ops module budget indices i j
          let nextIndex ← j + 1#usize
          Result.ok (.cont (next, nextBudget, nextIndices, nextIndex, result))
      else .ok (.done (module, budget, indices, status)) := by
  unfold runtime.compiler.initialize.lower_element_loop.body
  simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index module.module.env.elements.deref i segment
    (by simpa only [alloc.vec.Vec.deref, Slice.from_val] using found), bind_ok]
  cases status with
  | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
  | Ok unitValue =>
    cases unitValue
    simp only [core.result.Result.is_ok, bind_ok, ite_true]

/-- Source invocation and invariant callbacks for one element-value traversal. -/
structure ElementLoopInvariant (A : Type) where
  ops : runtime.platform.Alloc A
  before : runtime.compiler.ExecutableModule
  budget : runtime.compiler.Budget A
  indices : alloc.vec.Vec Usize
  i : Usize
  j : Usize
  status : core.result.Result Unit Itasca.error.VisitError
  segment : Itasca.metadata.Element
  found : before.module.env.elements.val[i.val]? = some segment
  bounded : j.val ≤ segment.init.val.length
  P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop
  advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize),
      current.module = before.module → cursor.val < segment.init.val.length → P current charged scratch cursor (.Ok ()) →
      ∀ result next nextBudget nextIndices (nextIndex : Usize),
        runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor =
          .ok (result, next, nextBudget, nextIndices) → nextIndex.val = cursor.val + 1 →
        P next nextBudget nextIndices nextIndex result
  finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → cursor.val ≤ segment.init.val.length → P current charged scratch cursor result →
      (cursor.val = segment.init.val.length ∨ result ≠ .Ok ()) → Q current charged scratch result
  initial : P before budget indices j status

/-- All normal loop returns transport the supplied invariant. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.inv {A : Type}
    (context : ElementLoopInvariant A)
    (after : runtime.compiler.ExecutableModule) (afterBudget : runtime.compiler.Budget A)
    (outIndices : alloc.vec.Vec Usize) (result : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element_loop context.ops context.before context.budget
      context.i context.indices context.j context.status = .ok (after, afterBudget, outIndices, result)) :
    context.Q after afterBudget outIndices result := by
  rcases context with ⟨ops, before, budget, indices, i, j, status, segment, found, bounded,
    P, Q, advance, finish, initial⟩
  let measure : ElementInitializerState A → Nat := fun (_, _, _, cursor, _) =>
    segment.init.val.length - cursor.val
  let invariant : ElementInitializerState A → Prop := fun (current, charged, scratch, cursor, result) =>
    current.module = before.module ∧ cursor.val ≤ segment.init.val.length ∧ P current charged scratch cursor result
  unfold runtime.compiler.initialize.lower_element_loop at called
  apply initializer_loop_success _ measure invariant
    (fun (current, charged, scratch, result) => Q current charged scratch result) ?_ _ ⟨rfl, bounded, initial⟩ _ called
  rintro ⟨current, charged, scratch, cursor, result⟩ ⟨source, position, prior⟩ flow body
  have selected : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
  simp only [uncurry_apply_pair, element_loop_body_eq ops current charged scratch i cursor result segment selected] at body
  by_cases more : cursor < alloc.vec.Vec.len segment.init
  · rw [if_pos more] at body
    have inside : cursor.val < segment.init.val.length := by scalar_tac
    cases result with
    | Err error =>
      have output := Result.ok_injective body
      subst flow
      exact finish current charged scratch cursor (.Err error) source position prior (.inr (by intro impossible; cases impossible))
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨nextResult, next, nextBudget, nextIndices⟩, lowered, tail⟩ := bind_ok_inv _ _ _ body
      obtain ⟨nextIndex, added, tail⟩ := bind_ok_inv _ _ _ tail
      have output := Result.ok_injective tail
      subst flow
      have increment : cursor + 1#usize ⦃ next => next.val = cursor.val + 1 ⦄ := by
        have size := segment.init.property
        step as ⟨next, nextEq⟩
        scalar_tac
      rw [added] at increment
      simp only [WP.spec_ok] at increment
      obtain ⟨actualSegment, expr, read, valueRead, effect⟩ :=
        runtime.compiler.initialize.lower_element_value.inv ops current next charged nextBudget scratch nextIndices i cursor nextResult lowered
      have nextSource := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
      refine ⟨⟨nextSource.trans source, ?_, advance current charged scratch cursor source inside prior
        nextResult next nextBudget nextIndices nextIndex lowered increment⟩, ?_⟩
      · omega
      · dsimp only [measure]
        omega
  · rw [if_neg more] at body
    have output := Result.ok_injective body
    subst flow
    have last : cursor.val = segment.init.val.length := by
      have notInside : ¬ cursor.val < segment.init.val.length := by scalar_tac
      omega
    exact finish current charged scratch cursor result source position prior (.inl last)

/-- Normal loop execution follows any normally returning callback contract.
The callback postcondition may express exact mappings or resource bounds. -/
@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.total {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError) (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment) (bounded : j.val ≤ segment.init.val.length)
    (P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop)
    (Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize →
      core.result.Result Unit Itasca.error.VisitError → Prop)
    (advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize),
      current.module = before.module → cursor.val < segment.init.val.length → P current charged scratch cursor (.Ok ()) →
      runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor
        ⦃ (result, next, nextBudget, nextIndices) => ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndices nextIndex result ⦄)
    (finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize) (result : core.result.Result Unit Itasca.error.VisitError),
      current.module = before.module → cursor.val ≤ segment.init.val.length → P current charged scratch cursor result →
      (cursor.val = segment.init.val.length ∨ result ≠ .Ok ()) → Q current charged scratch result)
    (initial : P before budget indices j status) :
    runtime.compiler.initialize.lower_element_loop ops before budget i indices j status
      ⦃ (after, afterBudget, outIndices, result) => Q after afterBudget outIndices result ⦄ := by
  let measure : ElementInitializerState A → Nat := fun (_, _, _, cursor, _) =>
    segment.init.val.length - cursor.val
  let invariant : ElementInitializerState A → Prop := fun (current, charged, scratch, cursor, result) =>
    current.module = before.module ∧ cursor.val ≤ segment.init.val.length ∧ P current charged scratch cursor result
  unfold runtime.compiler.initialize.lower_element_loop
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨current, charged, scratch, cursor, result⟩ ⟨source, position, prior⟩
    have selected : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
    simp only [uncurry_apply_pair, element_loop_body_eq ops current charged scratch i cursor result segment selected]
    by_cases more : cursor < alloc.vec.Vec.len segment.init
    · rw [if_pos more]
      have inside : cursor.val < segment.init.val.length := by scalar_tac
      cases result with
      | Err error =>
        exact WP.spec.ret (finish current charged scratch cursor (.Err error) source position prior
          (.inr (by intro impossible; cases impossible)))
      | Ok unitValue =>
        cases unitValue
        obtain ⟨⟨nextResult, next, nextBudget, nextIndices⟩, lowered, post⟩ := WP.spec_imp_exists
          (advance current charged scratch cursor source inside prior)
        simp only [lowered, bind_ok, uncurry_apply_pair]
        obtain ⟨actualSegment, expr, read, valueRead, effect⟩ :=
          runtime.compiler.initialize.lower_element_value.inv ops current next charged nextBudget scratch nextIndices i cursor nextResult lowered
        have nextSource := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) effect.frame
        have size := segment.init.property
        step as ⟨nextIndex, increment⟩
        refine ⟨⟨nextSource.trans source, ?_, post nextIndex (by scalar_tac)⟩, ?_⟩
        · scalar_tac
        · dsimp only [measure]
          scalar_tac
    · rw [if_neg more]
      have last : cursor.val = segment.init.val.length := by
        have notInside : ¬ cursor.val < segment.init.val.length := by scalar_tac
        omega
      exact WP.spec.ret (finish current charged scratch cursor result source position prior (.inl last))
  · exact ⟨rfl, bounded, initial⟩

/-- A successful callback at every remaining source index yields a successful
loop. The caller supplies its exact invariant and final postcondition. -/
@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.available {A : Type}
    (ops : runtime.platform.Alloc A) (before : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (indices : alloc.vec.Vec Usize) (i j : Usize)
    (segment : Itasca.metadata.Element)
    (found : before.module.env.elements.val[i.val]? = some segment) (bounded : j.val ≤ segment.init.val.length)
    (P : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Usize → Prop)
    (Q : runtime.compiler.ExecutableModule → runtime.compiler.Budget A → alloc.vec.Vec Usize → Prop)
    (advance : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize), current.module = before.module →
      cursor.val < segment.init.val.length → P current charged scratch cursor →
      runtime.compiler.initialize.lower_element_value ops current charged scratch i cursor
        ⦃ (result, next, nextBudget, nextIndices) => result = .Ok () ∧ ∀ nextIndex, nextIndex.val = cursor.val + 1 →
          P next nextBudget nextIndices nextIndex ⦄)
    (finish : ∀ (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A)
      (scratch : alloc.vec.Vec Usize) (cursor : Usize), current.module = before.module →
      cursor.val = segment.init.val.length → P current charged scratch cursor → Q current charged scratch)
    (initial : P before budget indices j) :
    runtime.compiler.initialize.lower_element_loop ops before budget i indices j (.Ok ())
      ⦃ (after, afterBudget, outIndices, result) => result = .Ok () ∧ Q after afterBudget outIndices ⦄ := by
  apply runtime.compiler.initialize.lower_element_loop.total ops before budget indices i j (.Ok ()) segment found bounded
    (fun current charged scratch cursor result => result = .Ok () ∧ P current charged scratch cursor)
    (fun current charged scratch result => result = .Ok () ∧ Q current charged scratch)
  · intro current charged scratch cursor source inside prior
    apply WP.spec_mono (advance current charged scratch cursor source inside prior.2)
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨accepted, post⟩ nextIndex increment
    exact ⟨accepted, post nextIndex increment⟩
  · intro current charged scratch cursor result source position prior stopped
    refine ⟨prior.1, ?_⟩
    have last := stopped.resolve_right (by intro rejected; exact rejected prior.1)
    exact finish current charged scratch cursor source last prior.2
  · exact ⟨rfl, initial⟩

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
  let expr := segment.init.val[j.val]'bound
  have valueFound : segment.init.val[j.val]? = some expr := List.getElem?_eq_getElem bound
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget, outIndices⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.lower_element_value.total ops law m budget indices i j segment expr found valueFound functionsFit capacity)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.lower_element_value.inv_selected ops m after budget afterBudget indices outIndices
    i j segment expr found valueFound status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_, growth.2⟩
  rw [frame]
  simp only [initializerSize]
  omega

/-- Element values accept from independent initializer typing, with separate
bounds for retained functions and the temporary initializer-index vector. -/
theorem initializer_element_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val < segment.init.val.length)
    (typed : Itasca.ModuleConstants.Valid module.module.env segment.init.val[valueIndex.val]
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2 ≤ budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound) (reserve : initializerSize module + 1 ≤ bound)
    (capacity : initializerSize module + 1 ≤ Usize.max)
    (indexCapacity : indices.length < Usize.max) (indexRequest : indices.length + 1 ≤ bound) :
    runtime.compiler.initialize.lower_element_value ops module budget indices index valueIndex ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.1.instructions.val = budget.instructions.val + 2 ∧
      out.2.2.1.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 = initializerSize module + 1 ∧ out.2.2.2.length = indices.length + 1 ⦄ := by
  let expr := segment.init.val[valueIndex.val]'inside
  have valueFound : segment.init.val[valueIndex.val]? = some expr := List.getElem?_eq_getElem inside
  have valid : Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem) := typed
  have vector : ∀ lo hi, expr = .V128 lo hi → Itasca.ModuleConstants.referenceValueType segment.elem = .V128 := by
    intros lo hi matching
    rw [matching] at valid
    generalize valueTypeEq : Itasca.ModuleConstants.referenceValueType segment.elem = valueType at valid ⊢
    cases valid
    rfl
  apply WP.spec_mono (runtime.compiler.initialize.lower_element_value.available ops bound available module budget indices index valueIndex
    segment expr lookup valueFound vector instructions codeRequest
    (by simp only [initializerSize, alloc.vec.Vec.length] at reserve ⊢; omega)
    (by simp only [initializerSize, alloc.vec.Vec.length] at capacity ⊢; omega)
    indexRequest indexCapacity)
  rintro ⟨status, after, afterBudget, outIndices⟩ ⟨accepted, count, limits, frame, mapped, function, certified, appended⟩
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨accepted, count, limits, moduleEq, ?_, ?_⟩
  · rw [frame]
    simp only [initializerSize, appended, List.length_append, List.length_singleton]
    omega
  · simp only [alloc.vec.Vec.length, mapped, List.length_append, List.length_singleton]

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
  let P := fun (current : runtime.compiler.ExecutableModule) (_ : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize)
      (_ : core.result.Result Unit Itasca.error.VisitError) =>
    initializerSize current + (segment.init.val.length - cursor.val) ≤ initializerSize m + (segment.init.val.length - j.val) ∧
    scratch.val.length ≤ cursor.val
  let Q := fun (current : runtime.compiler.ExecutableModule) (_ : runtime.compiler.Budget A) (_ : alloc.vec.Vec Usize)
      (_ : core.result.Result Unit Itasca.error.VisitError) =>
    current.module = m.module ∧ initializerSize current ≤ initializerSize m + (segment.init.val.length - j.val)
  refine WP.spec_mono (runtime.compiler.initialize.lower_element_loop.total ops m budget indices i j status segment
    found bound P Q ?_ ?_ ⟨Nat.le_refl _, indicesBound⟩) ?_
  · intro current charged scratch cursor source inside prior
    obtain ⟨size, scratchBound⟩ := prior
    have currentFound : current.module.env.elements.val[i.val]? = some segment := by simpa only [source] using found
    have lengthBound := segment.init.property
    apply WP.spec_mono (initializer_element_value_total ops law current charged scratch i cursor segment
      currentFound inside (by omega) (by omega))
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨nextSource, growth, indexGrowth⟩ nextIndex increment
    dsimp only at growth indexGrowth
    exact ⟨by omega, by omega⟩
  · intro current charged scratch cursor result source position prior stopped
    exact ⟨source, by have size := prior.1; omega⟩
  · rintro ⟨after, afterBudget, outIndices, result⟩ post
    exact post

/-- The complete remaining element-value loop accepts from independent source
typing and separate retained/scratch demand bounds. -/
theorem initializer_element_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (indices : alloc.vec.Vec Usize) (index valueIndex : Usize) (segment : Itasca.metadata.Element)
    (lookup : module.module.env.elements.val[index.val]? = some segment)
    (inside : valueIndex.val ≤ segment.init.val.length)
    (typed : ∀ expr ∈ segment.init.val, Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem))
    (instructions : budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ≤
      budget.limits.max_instructions.val)
    (codeRequest : 2 ≤ bound)
    (reserve : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ bound)
    (capacity : initializerSize module + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexCapacity : indices.length + (segment.init.val.length-valueIndex.val) ≤ Usize.max)
    (indexRequest : indices.length + (segment.init.val.length-valueIndex.val) ≤ bound) :
    runtime.compiler.initialize.lower_element_loop ops module budget index indices valueIndex (.Ok ()) ⦃ out =>
      out.2.2.2 = .Ok () ∧ out.1.module = module.module ∧ out.2.1.limits = budget.limits ∧
      initializerSize out.1 = initializerSize module + (segment.init.val.length-valueIndex.val) ∧
      out.2.2.1.length = indices.length + (segment.init.val.length-valueIndex.val) ∧
      out.2.1.instructions.val = budget.instructions.val + 2*(segment.init.val.length-valueIndex.val) ⦄ := by
  let P := fun (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) (cursor : Usize) =>
    charged.limits = budget.limits ∧
    initializerSize current + (segment.init.val.length - cursor.val) = initializerSize module + (segment.init.val.length - valueIndex.val) ∧
    scratch.length + (segment.init.val.length - cursor.val) = indices.length + (segment.init.val.length - valueIndex.val) ∧
    charged.instructions.val + 2 * (segment.init.val.length - cursor.val) =
      budget.instructions.val + 2 * (segment.init.val.length - valueIndex.val)
  let Q := fun (current : runtime.compiler.ExecutableModule) (charged : runtime.compiler.Budget A) (scratch : alloc.vec.Vec Usize) =>
    current.module = module.module ∧ charged.limits = budget.limits ∧
    initializerSize current = initializerSize module + (segment.init.val.length - valueIndex.val) ∧
    scratch.length = indices.length + (segment.init.val.length - valueIndex.val) ∧
    charged.instructions.val = budget.instructions.val + 2 * (segment.init.val.length - valueIndex.val)
  refine WP.spec_mono (runtime.compiler.initialize.lower_element_loop.available ops module budget indices index valueIndex segment
    lookup inside P Q ?_ ?_ ⟨rfl, rfl, rfl, rfl⟩) ?_
  · intro current charged scratch cursor source inside prior
    obtain ⟨limits, size, scratchSize, used⟩ := prior
    have currentLookup : current.module.env.elements.val[index.val]? = some segment := by simpa only [source] using lookup
    apply WP.spec_mono (initializer_element_value_available ops bound available current charged scratch index cursor segment
      currentLookup inside (by simpa only [source] using typed _ (List.getElem_mem inside))
      (by rw [limits]; omega) codeRequest (by omega) (by omega) (by omega) (by omega))
    rintro ⟨result, next, nextBudget, nextIndices⟩ ⟨accepted, usedAgain, limitsAgain, sourceAgain, sizeAgain, indicesAgain⟩
    dsimp only at accepted usedAgain limitsAgain sourceAgain sizeAgain indicesAgain
    refine ⟨accepted, ?_⟩
    intro nextIndex increment
    exact ⟨limitsAgain.trans limits, by omega, by omega, by omega⟩
  · intro current charged scratch cursor source last prior
    obtain ⟨limits, size, scratchSize, used⟩ := prior
    exact ⟨source, limits, by omega, by omega, by omega⟩
  · rintro ⟨after, afterBudget, outIndices, result⟩ post
    exact post

end Itasca.Runtime.Compiler
