import Itasca.Runtime.Compiler.Local.Initializer.ElementContracts
import Itasca.Runtime.Compiler.Local.Initializer.DataOffsetContracts
import Itasca.Runtime.Compiler.Local.Initializer.GlobalContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

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

end Itasca.Runtime.Compiler
