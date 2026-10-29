import Itasca.Runtime.Platform.DivSpec
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Interp.Relations.Readback
import Itasca.Runtime.Interp.Invocation.ResourceCauses
import Itasca.Runtime.Interp.Invocation.Checks
import Itasca.Runtime.Interp.Relations.Marshal
import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.Invocation.ReadbackOwnership
import Itasca.Runtime.Interp.Relations.TypeSlots
import Itasca.Runtime.Interp.Relations.Ensure
import Itasca.Runtime.Interp.Relations.ExecutionLoop

/-!
Invocation permits store extension during entry and execution, retaining the original function and signature through checked raw metadata prefixes.

Main declarations: `invoke_with_prefix_owned_causes_composition_mode` and `invoke_with_prefix_causes_composition_mode`. A direct consumer is `Interp.Invocation.PrefixDivergence`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

private theorem reserve_result {A T : Type} (allocator : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect allocator) (values : alloc.vec.Vec T) (extra : Usize) :
    ∃ answer : Bool, runtime.reserve allocator values extra = .ok
      ((if answer then .Ok () else .Err (.Exhausted .Allocation)), values) ∧
      allocator.reserve values extra = .ok (answer, values) := by
  obtain ⟨answer, reserved⟩ := law.reserve_eq values extra
  refine ⟨answer, ?_, reserved⟩
  cases answer <;> simp [runtime.reserve, reserved]

private theorem saturating_sub_value (x y : Usize) : (x.saturating_sub y).val = x.val - y.val := by
  simp only [UScalar.saturating_sub, Nat.zero_max]
  change (x.val - y.val) % 2 ^ UScalarTy.Usize.numBits = x.val - y.val
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- Invocation permits store extension during entry and execution, retaining the
original function and signature through checked raw metadata prefixes. -/
theorem invoke_with_prefix_owned_causes_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (cause : Prop)
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
    (entry : runtime.store.Store M → runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ error, InvocationResourceCause allocator exec store signature results error → errorProperty store error)
    (readbackError : ∀ after values, retained after → property after values →
      (∃ n : Usize, n.val = signature.results.length - results.length ∧
        allocator.reserve results n = .ok (false,results)) → errorProperty after (.Exhausted .Allocation))
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      DivSpec cause (runtime.interp.call memory hooks floats allocator prepared store p address 0#usize) fun out =>
        retained out.2.2.1 ∧ (out.1 = .Ok () → entry out.2.2.1 out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error))
    (executed : ∀ enteredStore prepared p, entry enteredStore prepared →
      DivSpec cause
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared enteredStore p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          FrameStorePrefix store afterStore ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Compiler.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    DivSpec cause
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue) ∧
        (∀ value ∈ out.2.2.2.2.val, OwnedBy out.2.2.1.id value)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  have tags : signature.params.val = args.val.map rawType := by
    have checked := check_values_accepts_iff memory store args (alloc.vec.Vec.deref signature.params)
    rw [accepted] at checked
    simp only [WP.spec_ok] at checked
    have matched : List.Forall₂ (ArgumentMatches store.id) args.val signature.params.val := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using checked.mp trivial
    exact argument_matches_rawtypes matched
  all_goals
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
      have cause : errorProperty store (.Exhausted .Values) := resourceError _ (by
        simp only [InvocationResourceCause]
        simp only [alloc.vec.Vec.deref, Slice.from_val] at overflow
        have limit : store.limits.max_values.val ≤ Usize.max := by scalar_tac
        omega)
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause, initial]
    | Ok params =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with type_slots_effect (alloc.vec.Vec.deref signature.results) as ⟨returns, returnCount⟩
      cases returns with
      | Err error =>
        obtain ⟨rfl, overflow⟩ := returnCount
        have cause : errorProperty store (.Exhausted .Values) := resourceError _ (by
          simp only [InvocationResourceCause]
          simp only [alloc.vec.Vec.deref, Slice.from_val] at overflow
          have limit : store.limits.max_values.val ≤ Usize.max := by scalar_tac
          omega)
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause, initial]
      | Ok returns =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, lift, bind_ok]
        step with ensure_effect allocator allocation exec (core.cmp.impls.OrdUsize.max params returns) store.limits.max_values
          as ⟨status, grown, growth⟩
        cases status with
        | Err error =>
          have allowed : errorProperty store error := by
            cases error <;> simp only [EnsureEffect] at growth
            all_goals try contradiction
            case Exhausted reason =>
              cases reason <;> simp only [EnsureEffect] at growth
              all_goals try contradiction
              case Values =>
                apply resourceError
                simp only [InvocationResourceCause]
                simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
                scalar_tac
              case Allocation =>
                obtain ⟨within, needed, unchanged, n, amount, reserved⟩ := growth
                apply resourceError
                apply Or.inl
                refine ⟨n, ?_, reserved⟩
                simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
                scalar_tac
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, allowed, initial]
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
          have capacity : (Compiler.encodeValues (args.val.map sourceValue)).length ≤ words.length := by
            have length : grown.slots.length = exec.slots.length + ((core.cmp.impls.OrdUsize.max params returns).val - exec.slots.length) := by
              change grown.slots.val.length = _
              rw [growth.2.1, List.length_append, List.length_replicate]
            rw [wordsEq, Compiler.encode_values_length]
            simp only [alloc.vec.Vec.deref, typeSlots, Slice.from_val] at paramCount
            have typeEq : (args.val.map sourceValue).map Compiler.valueType = signature.params.val.map sourceType := by
              rw [tags, List.map_map, List.map_map]
              congr 1
              funext value
              exact source_value_type value
            rw [typeEq]
            scalar_tac
          step with marshal_arguments words args signature.params store.id tags owned capacity
            as ⟨encoded, sameLength, represented⟩
          step with called ⟨store.id, encoded, frames, hostArgs, hostResults⟩ platform rfl empty represented
            as ⟨status, entered, calledStore, calledPlatform, calledRetained, enteredProof, callError⟩
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, callError error rfl, calledRetained]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with executed calledStore entered calledPlatform (enteredProof rfl)
              as ⟨id, finalWords, finalFrames, finalArgs, finalHostResults, finalStore, finalPlatform, status, post⟩
            obtain ⟨kept,finalRetained,finished,loopError⟩ := post
            cases status with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, loopError error rfl, finalRetained]
            | Ok unit =>
              cases unit
              obtain ⟨values, types, wellFormed, fits, represented, satisfied⟩ := finished rfl
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              have finalOwner : address.store = finalStore.id := owner.trans kept.identity.symm
              have finalFunction : finalStore.funcs.val[address.index.val]? = some function := kept.function_lookup hf
              have finalSignature : finalStore.types.val[function.signature.val]? = some signature := kept.type_lookup hs
              step with func_type_lookup memory finalStore address function signature finalOwner finalFunction finalSignature as ⟨found,same⟩
              subst found
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              let additional := core.num.Usize.saturating_sub signature.results.len results.len
              obtain ⟨answer, reserved, actualReserve⟩ := reserve_result allocator allocation results additional
              rw [reserved, bind_ok]
              cases answer with
              | false =>
                have cause : errorProperty finalStore (.Exhausted .Allocation) := readbackError finalStore values finalRetained satisfied
                  ⟨additional, by simp [additional, core.num.Usize.saturating_sub, saturating_sub_value], actualReserve⟩
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause, finalRetained]
              | true =>
                simp only [ite_true, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
                step with runtime_clear results as ⟨emptyResults, empty⟩
                step with read_results_owned finalWords finalStore emptyResults signature.results values empty types wellFormed fits represented
                  as ⟨returnedStore, returnedResults, sameStore, sameResults, resultOwners⟩
                subst returnedStore
                try simp only [DivSpec.ok_iff]
                exact ⟨finalRetained, (fun _ => ⟨by simpa only [sameResults] using satisfied,resultOwners⟩), by intro error impossible; cases impossible⟩

theorem invoke_with_prefix_causes_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (cause : Prop)
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
    (entry : runtime.store.Store M → runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after error, InvocationResourceCause allocator exec store signature results error → errorProperty after error)
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      DivSpec cause (runtime.interp.call memory hooks floats allocator prepared store p address 0#usize) fun out =>
        retained out.2.2.1 ∧ (out.1 = .Ok () → entry out.2.2.1 out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error))
    (executed : ∀ enteredStore prepared p, entry enteredStore prepared →
      DivSpec cause
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared enteredStore p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          FrameStorePrefix store afterStore ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Compiler.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    DivSpec cause
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  apply DivSpec.mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator cause allocation
    exec store platform address function signature args results owner hf hs accepted owned entry retained initial
    property errorProperty (fun error cause => resourceError store error cause)
    (fun after values kept satisfied refused => resourceError after _ (Or.inr refused)) called executed)
  rintro out ⟨kept,success,errors⟩
  exact ⟨kept,fun accepted => (success accepted).1,errors⟩

end Itasca.Runtime.Interp
