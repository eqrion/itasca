import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeResourceCauses
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.InvocationSetup
import Exec.Interp.Relations.Readback
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop

namespace Exec.Interp
open Aeneas Aeneas.Std

private theorem rawtypes_of_matches {id : Usize} {args : List runtime.Value} {types : List Itasca.types.ValueType}
    (matched : List.Forall₂ (ArgumentMatches id) args types) : types = args.map rawType := by
  induction matched with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.2, ih]

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

/-- Mutable invocation preserves exact setup and result-vector refusal witnesses,
with final-store-dependent postconditions for the executed body. -/
theorem invoke_with_mutable_causes_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allowDivergence : Bool)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after error, InvocationResourceCause allocator exec store signature results error → errorProperty after error)
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      InvocationWP allowDivergence
        (runtime.interp.invoke_with_loop2 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    InvocationWP allowDivergence
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  have tags : signature.params.val = args.val.map rawType := by
    have checked := check_values_accepts_iff memory store args (alloc.vec.Vec.deref signature.params)
    rw [accepted] at checked
    simp only [WP.spec_ok] at checked
    have matched : List.Forall₂ (ArgumentMatches store.id) args.val signature.params.val := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using checked.mp trivial
    exact rawtypes_of_matches matched
  cases allowDivergence
  all_goals
    simp only [InvocationWP, Bool.false_eq_true, ite_false, ite_true] at executed ⊢
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
      have cause : errorProperty store (.Exhausted .Values) := resourceError store _ (by
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
        have cause : errorProperty store (.Exhausted .Values) := resourceError store _ (by
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
                apply resourceError store
                simp only [InvocationResourceCause]
                simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
                scalar_tac
              case Allocation =>
                obtain ⟨within, needed, unchanged, n, amount, reserved⟩ := growth
                apply resourceError store
                apply Or.inl
                refine ⟨n, ?_, reserved⟩
                simp only [alloc.vec.Vec.deref, Slice.from_val] at paramCount returnCount
                scalar_tac
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, allowed, initial]
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with clear_frames grown as ⟨words, frames, hostArgs, hostResults, wordsEq, empty, argsEq, resultsEq⟩
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
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, callError error rfl, initial]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with executed entered calledPlatform (enteredProof rfl)
              as ⟨id, finalWords, finalFrames, finalArgs, finalHostResults, finalStore, finalPlatform, status, sameIdentity,sameFunctions,sameTypes,finalRetained,finished,loopError⟩
            cases status with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, loopError error rfl, finalRetained]
            | Ok unit =>
              cases unit
              obtain ⟨values, types, wellFormed, fits, represented, satisfied⟩ := finished rfl
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              have finalOwner : address.store = finalStore.id := owner.trans sameIdentity.symm
              have finalFunction : finalStore.funcs.val[address.index.val]? = some function := by simpa only [sameFunctions] using hf
              have finalSignature : finalStore.types.val[function.signature.val]? = some signature := by simpa only [sameTypes] using hs
              step with func_type_lookup memory finalStore address function signature finalOwner finalFunction finalSignature as ⟨found,same⟩
              subst found
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              let additional := core.num.Usize.saturating_sub signature.results.len results.len
              obtain ⟨answer, reserved, actualReserve⟩ := reserve_result allocator allocation results additional
              rw [reserved, bind_ok]
              cases answer with
              | false =>
                have cause : errorProperty finalStore (.Exhausted .Allocation) := resourceError finalStore _ (Or.inr
                  ⟨additional, by simp [additional, core.num.Usize.saturating_sub, saturating_sub_value], actualReserve⟩)
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause, finalRetained]
              | true =>
                simp only [ite_true, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
                step with clear_results results as ⟨emptyResults, empty⟩
                step with read_results finalWords finalStore emptyResults signature.results values empty types wellFormed fits represented
                  as ⟨returnedStore, returnedResults, sameStore, sameResults⟩
                subst returnedStore
                try simp only [WP.dspec_ok, WP.spec_ok]
                exact ⟨finalRetained, (fun _ => by simpa only [sameResults] using satisfied), by intro error impossible; cases impossible⟩

theorem InvocationResourceCause.kind {A M : Type} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {signature : Itasca.types.FuncType}
    {results : alloc.vec.Vec runtime.Value} {error : runtime.ExecError}
    (cause : InvocationResourceCause allocator exec store signature results error) :
    error=.Exhausted .Values ∨ error=.Exhausted .Allocation := by
  cases error <;> simp only [InvocationResourceCause] at cause
  all_goals try contradiction
  case Exhausted reason => cases reason <;> simp_all [InvocationResourceCause]

theorem invoke_with_mutable_causes_composition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.interp.Execution → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → Prop)
    (resourceError : ∀ after error, InvocationResourceCause allocator exec store signature results error → errorProperty after error)
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.2.2.1 = store ∧ (out.1 = .Ok () → entry out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty store error) ⦄)
    (executed : ∀ prepared p, entry prepared →
      WP.dspec
        (runtime.interp.invoke_with_loop2 memory hooks floats allocator prepared store p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          afterStore.id = store.id ∧ afterStore.funcs = store.funcs ∧ afterStore.types = store.types ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map sourceType = values.map Code.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    WP.dspec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  exact invoke_with_mutable_causes_composition_mode memory hooks floats allocator true allocation exec store platform
    address function signature args results owner hf hs accepted owned entry retained initial property errorProperty resourceError called executed

end Exec.Interp
