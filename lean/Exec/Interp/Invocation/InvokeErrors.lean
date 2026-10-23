import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

private theorem reserve_result {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)), values) := by
  obtain ⟨answer, reserved⟩ := law.reserve_eq values extra
  refine ⟨answer, ?_⟩
  cases answer <;> simp [runtime.reserve, reserved]

/-- Preserve both success and error predicates through actual invocation.
Preparation and result-vector allocation can add resource errors. Local call
and loop contracts must account for every other error. -/
theorem invoke_with_error_composition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop) (property : List val → Prop)
    (errorProperty : runtime.ExecError → Prop)
    (resourceError : ∀ reason, errorProperty (.Exhausted reason))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      WP.dspec
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) => afterStore = store ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property values) ∧
          (∀ error, status = .Err error → errorProperty error))) :
    WP.dspec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => out.2.2.1 = store ∧ (out.1 = .Ok () → property (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty error)) := by
  have tags : signature.params.val = args.val.map rawType := by
    have checked := check_values_accepts_iff memory store args (alloc.vec.Vec.deref signature.params)
    rw [accepted] at checked
    simp only [WP.spec_ok] at checked
    have matched : List.Forall₂ (ArgumentMatches store.id) args.val signature.params.val := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using checked.mp trivial
    exact argument_matches_rawtypes matched
  unfold runtime.interp.invoke_with
  step with func_type_lookup memory store address function signature owner hf hs as ⟨found, same⟩
  subst found
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [accepted]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  step with type_slots_effect (alloc.vec.Vec.deref signature.params) as ⟨params, paramCount⟩
  cases params with
  | Err error =>
    obtain ⟨rfl, overflow⟩ := paramCount
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, resourceError]
  | Ok params =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with type_slots_effect (alloc.vec.Vec.deref signature.results) as ⟨returns, returnCount⟩
    cases returns with
    | Err error =>
      obtain ⟨rfl, overflow⟩ := returnCount
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, resourceError]
    | Ok returns =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
      step with ensure_effect allocator allocation exec (core.cmp.impls.OrdUsize.max params returns) store.limits.max_values
        as ⟨status, grown, growth⟩
      cases status with
      | Err error =>
        have allowed : errorProperty error := by
          cases error <;> simp only [EnsureEffect] at growth
          all_goals try contradiction
          case Exhausted reason => exact resourceError reason
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, allowed]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with runtime_clear grown.frames as ⟨frames, empty⟩
        generalize sameWords : grown.slots = words
        generalize sameArgs : grown.host_args = hostArgs
        generalize sameResults : grown.host_results = hostResults
        have wordsEq := sameWords.symm
        have argsEq := sameArgs.symm
        have resultsEq := sameResults.symm
        have capacity : (Code.encodeValues (args.val.map sourceValue)).length ≤ words.length := by
          have length : grown.slots.length = exec.slots.length + ((core.cmp.impls.OrdUsize.max params returns).val - exec.slots.length) := by
            change grown.slots.val.length = _
            rw [growth.2.1, List.length_append, List.length_replicate]
          rw [wordsEq, Code.encodeValues_length]
          simp only [alloc.vec.Vec.deref, typeSlots, Slice.from_val] at paramCount
          have typeEq : (args.val.map sourceValue).map Code.valueType = signature.params.val.map sourceType := by
            rw [tags, List.map_map, List.map_map]
            congr 1
            funext value
            exact sourceValue_type value
          rw [typeEq]
          scalar_tac
        step with marshal_arguments words args signature.params store.id tags owned capacity
          as ⟨encoded, sameLength, represented⟩
        step with called ⟨store.id, encoded, frames, hostArgs, hostResults⟩ platform rfl empty represented
          as ⟨status, entered, calledStore, calledPlatform, storeSame, enteredProof, callError⟩
        subst calledStore
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, callError error rfl]
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with executed entered calledPlatform (enteredProof rfl)
            as ⟨id, finalWords, finalFrames, finalArgs, finalHostResults, finalStore, finalPlatform, status, post⟩
          obtain ⟨storeSame, finished, loopError⟩ := post
          subst finalStore
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, loopError error rfl]
          | Ok unit =>
            cases unit
            obtain ⟨values, types, wellFormed, fits, represented, satisfied⟩ := finished rfl
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with func_type_lookup memory store address function signature owner hf hs as ⟨found, same⟩
            subst found
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            let additional := core.num.Usize.saturating_sub signature.results.len results.len
            obtain ⟨answer, reserved⟩ := reserve_result allocator allocation results additional
            rw [reserved, bind_ok]
            cases answer with
            | false =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, resourceError]
            | true =>
              simp only [ite_true, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
              step with runtime_clear results as ⟨emptyResults, empty⟩
              step with read_results finalWords store emptyResults signature.results values empty types wellFormed fits represented
                as ⟨returnedStore, returnedResults, sameStore, sameResults⟩
              subst returnedStore
              simp only [WP.dspec_ok, WP.spec_ok]
              exact ⟨trivial, (fun _ => by simpa only [sameResults] using satisfied), by intro error impossible; cases impossible⟩

end Exec.Interp
