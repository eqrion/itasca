import Itasca.Runtime.Compiler.Local.Initializer

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

private abbrev SegmentStatus := core.result.Result Unit Itasca.error.VisitError
private abbrev SegmentState (A : Type) := runtime.compiler.Budget A × Usize × SegmentStatus × runtime.bytecode.CompiledFunction
private abbrev SegmentResult (A : Type) := runtime.compiler.Budget A × SegmentStatus × runtime.bytecode.CompiledFunction

/-- Common indexed emission traversal for source element and data segments. -/
structure InitializerSegmentLoop (A : Type) where
  body : SegmentState A → Result (ControlFlow (SegmentState A) (SegmentResult A))
  callback : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize →
    Result (SegmentStatus × runtime.compiler.Budget A × runtime.bytecode.CompiledFunction)
  count : Usize
  body_eq : ∀ budget cursor status function,
    body (budget, cursor, status, function) =
      if cursor < count then
        match status with
        | .Err _ => .ok (.done (budget, status, function))
        | .Ok () => do
          let (result, nextBudget, nextFunction) ← callback budget function cursor
          let nextIndex ← cursor + 1#usize
          Result.ok (.cont (nextBudget, nextIndex, result, nextFunction))
      else .ok (.done (budget, status, function))

/-- The state predicate and terminal projection for normal segment-loop returns. -/
structure SegmentLoopInvariant (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  status : SegmentStatus
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → SegmentStatus → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → SegmentStatus → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor (.Ok ()) →
    ∀ result nextBudget nextFunction (nextIndex : Usize),
      rules.callback charged current cursor = .ok (result, nextBudget, nextFunction) →
      nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex result
  finish : ∀ charged current cursor result, P charged current cursor result →
    (rules.count.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q charged current result
  initial : P budget function index status

theorem InitializerSegmentLoop.inv {A : Type} (context : SegmentLoopInvariant A)
    (afterBudget : runtime.compiler.Budget A) (after : runtime.bytecode.CompiledFunction) (result : SegmentStatus)
    (called : loop context.rules.body (context.budget, context.index, context.status, context.function) =
      .ok (afterBudget, result, after)) : context.Q afterBudget after result := by
  rcases context with ⟨rules, budget, function, index, status, P, Q, advance, finish, initial⟩
  let measure : SegmentState A → Nat := fun (_, cursor, _, _) => rules.count.val - cursor.val
  let invariant : SegmentState A → Prop := fun (charged, cursor, result, current) => P charged current cursor result
  apply initializer_loop_success _ measure invariant
    (fun (charged, result, current) => Q charged current result) ?_ _ initial _ called
  rintro ⟨charged, cursor, result, current⟩ prior flow body
  rw [rules.body_eq] at body
  by_cases more : cursor < rules.count
  · rw [if_pos more] at body
    have inside : cursor.val < rules.count.val := by scalar_tac
    cases result with
    | Err error =>
      have output := Result.ok_injective body
      subst flow
      exact finish charged current cursor (.Err error) prior (.inr (by intro impossible; cases impossible))
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨nextResult, nextBudget, nextFunction⟩, lowered, tail⟩ := bind_ok_inv _ _ _ body
      obtain ⟨nextIndex, added, tail⟩ := bind_ok_inv _ _ _ tail
      have output := Result.ok_injective tail
      subst flow
      have increment : cursor + 1#usize ⦃ next => next.val = cursor.val + 1 ⦄ := by
        step as ⟨next, nextEq⟩
        scalar_tac
      rw [added] at increment
      simp only [WP.spec_ok] at increment
      refine ⟨advance charged current cursor inside prior nextResult nextBudget nextFunction nextIndex lowered increment, ?_⟩
      dsimp only [measure]
      omega
  · rw [if_neg more] at body
    have output := Result.ok_injective body
    subst flow
    have last : rules.count.val ≤ cursor.val := by scalar_tac
    exact finish charged current cursor result prior (.inl last)

/-- Callback normality and a decreasing index certify complete loop normality. -/
structure SegmentLoopTotal (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  status : SegmentStatus
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → SegmentStatus → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → SegmentStatus → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor (.Ok ()) →
    rules.callback charged current cursor ⦃ (result, nextBudget, nextFunction) =>
      ∀ nextIndex, nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex result ⦄
  finish : ∀ charged current cursor result, P charged current cursor result →
    (rules.count.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q charged current result
  initial : P budget function index status

@[step] theorem InitializerSegmentLoop.total {A : Type} (context : SegmentLoopTotal A) :
    loop context.rules.body (context.budget, context.index, context.status, context.function)
      ⦃ (afterBudget, result, after) => context.Q afterBudget after result ⦄ := by
  rcases context with ⟨rules, budget, function, index, status, P, Q, advance, finish, initial⟩
  let measure : SegmentState A → Nat := fun (_, cursor, _, _) => rules.count.val - cursor.val
  let invariant : SegmentState A → Prop := fun (charged, cursor, result, current) => P charged current cursor result
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨charged, cursor, result, current⟩ prior
    rw [rules.body_eq]
    by_cases more : cursor < rules.count
    · rw [if_pos more]
      have inside : cursor.val < rules.count.val := by scalar_tac
      cases result with
      | Err error => exact WP.spec.ret (finish charged current cursor (.Err error) prior
          (.inr (by intro impossible; cases impossible)))
      | Ok unitValue =>
        cases unitValue
        obtain ⟨⟨nextResult, nextBudget, nextFunction⟩, lowered, post⟩ :=
          WP.spec_imp_exists (advance charged current cursor inside prior)
        simp only [lowered, bind_ok, uncurry_apply_pair]
        step as ⟨nextIndex, increment⟩
        refine ⟨post nextIndex (by scalar_tac), ?_⟩
        dsimp only [measure]
        scalar_tac
    · rw [if_neg more]
      have last : rules.count.val ≤ cursor.val := by scalar_tac
      exact WP.spec.ret (finish charged current cursor result prior (.inl last))
  · exact initial

/-- Successful segment callbacks yield a successful complete traversal. -/
structure SegmentLoopAvailable (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  bounded : index.val ≤ rules.count.val
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor →
    rules.callback charged current cursor ⦃ (result, nextBudget, nextFunction) => result = .Ok () ∧
      ∀ nextIndex, nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex ⦄
  finish : ∀ charged current cursor, cursor.val = rules.count.val → P charged current cursor → Q charged current
  initial : P budget function index

@[step] theorem InitializerSegmentLoop.available {A : Type} (context : SegmentLoopAvailable A) :
    loop context.rules.body (context.budget, context.index, .Ok (), context.function)
      ⦃ (afterBudget, result, after) => result = .Ok () ∧ context.Q afterBudget after ⦄ := by
  rcases context with ⟨rules, budget, function, index, bounded, P, Q, advance, finish, initial⟩
  apply InitializerSegmentLoop.total
    { rules := rules, budget := budget, function := function, index := index, status := .Ok (),
      P := fun charged current cursor result => result = .Ok () ∧ cursor.val ≤ rules.count.val ∧ P charged current cursor,
      Q := fun charged current result => result = .Ok () ∧ Q charged current,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor inside prior
    apply WP.spec_mono (advance charged current cursor inside prior.2.2)
    rintro ⟨result, nextBudget, nextFunction⟩ ⟨accepted, post⟩ nextIndex increment
    exact ⟨accepted, by omega, post nextIndex increment⟩
  · intro charged current cursor result prior stopped
    have last := stopped.resolve_right (by intro rejected; exact rejected prior.1)
    exact ⟨prior.1, finish charged current cursor (by omega) prior.2.2⟩
  · exact ⟨rfl, bounded, initial⟩

/-- Indexed initialization-code emission for source element segments. -/
def initializerEmitElementLoop {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) : InitializerSegmentLoop A where
  body := fun (budget, cursor, status, function) =>
    runtime.compiler.initialize.lower_loop3.body ops module budget cursor status function
  callback := fun budget function cursor => runtime.compiler.initialize.emit_element ops module budget function cursor
  count := alloc.vec.Vec.len module.module.env.elements
  body_eq := by
    intro budget cursor status function
    unfold runtime.compiler.initialize.lower_loop3.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
    have size : Slice.len module.module.env.elements.deref = alloc.vec.Vec.len module.module.env.elements := by
      simp only [alloc.vec.Vec.deref, Slice.len, alloc.vec.Vec.len, Slice.from_val]
    rw [size]
    cases status with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]

/-- Indexed initialization-code emission for source data segments. -/
def initializerEmitDataLoop {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) : InitializerSegmentLoop A where
  body := fun (budget, cursor, status, function) =>
    runtime.compiler.initialize.lower_loop4.body ops module budget cursor status function
  callback := fun budget function cursor => runtime.compiler.initialize.emit_data ops module budget function cursor
  count := alloc.vec.Vec.len module.module.tail.data
  body_eq := by
    intro budget cursor status function
    unfold runtime.compiler.initialize.lower_loop4.body
    simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
    cases status with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]

end Itasca.Runtime.Compiler
