import Exec.Code.Local.Initializer.InitializerMappings

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Partial correctness for actual loops with a decreasing successful body.
This theorem makes no termination claim for a failing or divergent body. -/
theorem initializer_loop_success {S O : Type} (body : S → Result (ControlFlow S O))
    (measure : S → Nat) (inv : S → Prop) (post : O → Prop)
    (sound : ∀ state, inv state → ∀ flow, body state = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out)
    (state : S) (initial : inv state) (out : O) (success : loop body state = .ok out) : post out := by
  suffices ∀ n state, measure state = n → inv state → loop body state = .ok out → post out by
    exact this (measure state) state rfl initial success
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro current hmeasure hcurrent returned
    rw [loop.eq_def] at returned
    obtain ⟨flow, step, rest⟩ := initializer_bind_success returned
    have effect := sound current hcurrent flow step
    cases flow with
    | done answer =>
      have same := Result.ok_injective rest
      subst answer
      exact effect
    | cont next =>
      exact ih (measure next) (by simpa [hmeasure] using effect.2) next rfl effect.1 rest

/-- Indexed source expressions and their retained synthetic functions. -/
def InitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (expressions : List Itasca.types.ConstExpr) (ty : Itasca.types.ValueType)
    (indices : List Usize) : Prop :=
  List.Forall₂ (fun expr index => InitializerAt functions index expr ty) expressions indices

theorem InitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {expressions ty indices}
    (entries : InitializerEntries before expressions ty indices) :
    InitializerEntries after expressions ty indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalInitializerEntries (functions : List runtime.bytecode.CompiledFunction)
    (globals : List Itasca.module.Global) (indices : List Usize) : Prop :=
  List.Forall₂ (fun global index => InitializerAt functions index global.init global.gtype.valtype)
    globals indices

theorem GlobalInitializerEntries.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {globals indices}
    (entries : GlobalInitializerEntries before globals indices) :
    GlobalInitializerEntries after globals indices := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def GlobalMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, global_initializers := current.global_initializers } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  GlobalInitializerEntries current.functions.val (before.module.env.globals.val.take count)
    current.global_initializers.val

theorem global_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val < before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_global ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : GlobalMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, entries⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let global := before.module.env.globals.val[index.val]
  have found : current.module.env.globals.val[index.val]? = some global := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨function, fnIndex, cert, position, changed, functions, indices⟩ :=
    initializer_lower_global ops law current after budget budgetAfter index global found success
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
  · unfold GlobalInitializerEntries at extended ⊢
    rw [List.take_add_one, indices]
    have single : List.Forall₂
        (fun global index => InitializerAt after.functions.val index global.init global.gtype.valtype)
        [global] [fnIndex] := by
      refine .cons ?_ .nil
      refine ⟨function, ?_, cert⟩
      rw [functions, position]
      simp
    simpa [List.getElem?_eq_getElem bound, global] using List.rel_append extended single

/-- Successful completion of the actual global initializer loop retains a
certificate for each source global, with exact module-field preservation. -/
theorem initializer_global_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : GlobalMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.env.globals.val.length)
    (success : runtime.compiler.initialize.lower_loop0 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    GlobalMappingPrefix before after before.module.env.globals.val.length := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.env.globals.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.env.globals.val.length ∧
      GlobalMappingPrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → GlobalMappingPrefix before p.1 before.module.env.globals.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop0.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop0.body at body
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.globals, bind_ok] at body
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
        have hmore : i.val < before.module.env.globals.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.env.globals.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := global_mapping_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.env.globals.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop0.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

end Itasca.Runtime.Code
