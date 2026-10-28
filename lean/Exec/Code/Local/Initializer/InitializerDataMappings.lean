import Exec.Code.Local.Initializer.InitializerElementLoop

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def sourceDataOffset (segment : Itasca.module.Data) : Option Itasca.types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive => none

theorem initializer_lower_data {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (module after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (segment : Itasca.module.Data)
    (found : module.module.tail.data.val[index.val]? = some segment)
    (success : runtime.compiler.initialize.lower_data_offset ops module budget index =
      .ok (.Ok (), after, budgetAfter)) :
    ∃ offset,
      after = { module with functions := after.functions, data_offsets := after.data_offsets } ∧
      after.functions.val.take module.functions.length = module.functions.val ∧
      after.data_offsets.val = module.data_offsets.val ++ [offset] ∧
      OffsetInitializer after.functions.val (sourceDataOffset segment) offset := by
  cases mode : segment.mode with
  | Passive =>
    obtain ⟨changed, offsets⟩ := initializer_lower_data_passive ops law module after budget budgetAfter index
      segment found mode success
    have functions := congrArg runtime.compiler.ExecutableModule.functions changed
    dsimp only at functions
    refine ⟨none, ?_, ?_, offsets, ?_⟩
    · rw [changed]
    · simp [functions]
    · simp [OffsetInitializer, sourceDataOffset, mode]
  | Active memory expr =>
    obtain ⟨function, fnIndex, certificate, position, changed, functions, offsets⟩ :=
      initializer_lower_data_active ops law module after budget budgetAfter index segment memory expr found mode success
    refine ⟨some fnIndex, changed, ?_, offsets, ?_⟩
    · simp [functions]
    · simp only [OffsetInitializer, sourceDataOffset, mode]
      refine ⟨function, ?_, certificate⟩
      rw [functions, position]
      simp

def DataOffsetMappings (functions : List runtime.bytecode.CompiledFunction)
    (segments : List Itasca.module.Data) (offsets : List (Option Usize)) : Prop :=
  List.Forall₂ (fun segment offset => OffsetInitializer functions (sourceDataOffset segment) offset)
    segments offsets

theorem DataOffsetMappings.extend {before after : List runtime.bytecode.CompiledFunction}
    (prefixEq : after.take before.length = before) {segments offsets}
    (entries : DataOffsetMappings before segments offsets) :
    DataOffsetMappings after segments offsets := by
  induction entries with
  | nil => exact .nil
  | cons cert rest ih => exact .cons (cert.extend prefixEq) ih

def DataMappingPrefix (before current : runtime.compiler.ExecutableModule) (count : Nat) : Prop :=
  current = { before with functions := current.functions, data_offsets := current.data_offsets } ∧
  current.functions.val.take before.functions.length = before.functions.val ∧
  DataOffsetMappings current.functions.val (before.module.tail.data.val.take count) current.data_offsets.val

theorem data_mapping_append {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataMappingPrefix before current index.val)
    (bound : index.val < before.module.tail.data.val.length)
    (success : runtime.compiler.initialize.lower_data_offset ops current budget index =
      .ok (.Ok (), after, budgetAfter)) : DataMappingPrefix before after (index.val + 1) := by
  obtain ⟨unchanged, prefixEq, offsets⟩ := prefixInv
  have source := congrArg runtime.compiler.ExecutableModule.module unchanged
  dsimp only at source
  let segment := before.module.tail.data.val[index.val]
  have found : current.module.tail.data.val[index.val]? = some segment := by
    rw [source]
    exact List.getElem?_eq_getElem bound
  obtain ⟨offset, changed, functions, offsetList, offsetCert⟩ :=
    initializer_lower_data ops law current after budget budgetAfter index segment found success
  have extendedOffsets := offsets.extend functions
  refine ⟨?_, initializer_prefix_trans prefixEq functions, ?_⟩
  · rw [changed]
    conv_lhs => rw [unchanged]
  · unfold DataOffsetMappings at extendedOffsets ⊢
    rw [List.take_add_one, offsetList]
    simpa [List.getElem?_eq_getElem bound, segment] using
      List.rel_append extendedOffsets (.cons offsetCert .nil)

theorem initializer_data_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before current after : runtime.compiler.ExecutableModule)
    (budget budgetAfter : runtime.compiler.Budget A) (index : Usize)
    (prefixInv : DataMappingPrefix before current index.val)
    (bound : index.val ≤ before.module.tail.data.val.length)
    (success : runtime.compiler.initialize.lower_loop2 ops current budget index (.Ok ()) =
      .ok (after, budgetAfter, .Ok ())) :
    DataMappingPrefix before after before.module.tail.data.val.length := by
  classical
  let measure := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    if p.2.2.2 = .Ok () then before.module.tail.data.val.length - p.2.2.1.val + 1 else 0
  let inv := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A × Usize ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2.2 = .Ok () → p.2.2.1.val ≤ before.module.tail.data.val.length ∧
      DataMappingPrefix before p.1 p.2.2.1.val
  let post := fun p : runtime.compiler.ExecutableModule × runtime.compiler.Budget A ×
      core.result.Result Unit Itasca.error.VisitError =>
    p.2.2 = .Ok () → DataMappingPrefix before p.1 before.module.tail.data.val.length
  have sound : ∀ state, inv state → ∀ flow,
      runtime.compiler.initialize.lower_loop2.body ops state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok flow →
      match flow with
      | .cont next => inv next ∧ measure next < measure state
      | .done out => post out := by
    rintro ⟨module, b, i, status⟩ hinv flow body
    dsimp only [inv] at hinv
    unfold runtime.compiler.initialize.lower_loop2.body at body
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok] at body
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
        have hmore : i.val < before.module.tail.data.val.length := by
          simpa [alloc.vec.Vec.deref] using more
        obtain ⟨⟨result, nextModule, nextBudget⟩, lowered, rest⟩ := initializer_bind_success body
        obtain ⟨nextIndex, added, rest⟩ := initializer_bind_success rest
        have output := Result.ok_injective rest
        subst flow
        have addSpec : i + 1#usize ⦃ next => next.val = i.val + 1 ⦄ := by
          have size := before.module.tail.data.property
          step as ⟨next, hnext⟩
          scalar_tac
        rw [added] at addSpec
        simp only [WP.spec_ok] at addSpec
        cases result with
        | Err error => simp [inv, measure]
        | Ok unit =>
          cases unit
          have nextPrefix := data_mapping_append ops law before module nextModule b nextBudget i prefixInv hmore lowered
          refine ⟨?_, ?_⟩
          · dsimp only [inv]
            intro _
            exact ⟨by omega, by simpa [addSpec] using nextPrefix⟩
          · simp only [measure, ↓reduceIte]
            omega
      · rename_i stopped
        have stop : i.val = before.module.tail.data.val.length := by
          simp [alloc.vec.Vec.deref] at stopped
          omega
        have output := Result.ok_injective body
        subst flow
        dsimp only [post]
        intro _
        simpa [stop] using prefixInv
  have result := initializer_loop_success
    (fun p => runtime.compiler.initialize.lower_loop2.body ops p.1 p.2.1 p.2.2.1 p.2.2.2)
    measure inv post (by
      intro state hstate flow hflow
      cases flow <;> exact sound state hstate _ hflow) (current, budget, index, .Ok ()) (by exact fun _ => ⟨bound, prefixInv⟩)
    (after, budgetAfter, .Ok ()) success
  exact result rfl

end Itasca.Runtime.Code
