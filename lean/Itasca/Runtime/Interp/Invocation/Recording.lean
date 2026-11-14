import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.SuspendedPoint
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Support.Result
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.Interp.Calls.CallRecording

/-!
Sections, each formerly its own module: Checks, Divergence, ReadbackOwnership, ResourceCauses, PrefixCauses, PrefixDivergence, MutableCauses, LoopRecording, LoopRecordingFacts, Recording.
-/

/-! ## Checks -/

section

/-! Public invocation rejection before execution begins. These conclusions
preserve execution state, store, platform, and the caller's result vector. -/
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem func_type_lookup {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (func : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.wasm_types.FuncType)
    (owner : func.store = store.id)
    (hf : store.funcs.val[func.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature) :
    runtime.store.Store.func_type memory store func ⦃ out => out = .Ok signature ⦄ := by
  unfold runtime.store.Store.func_type
  simp only [runtime.store.Store.check, owner, ↓reduceIte, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  step with vec_index_given store.funcs func.index function hf as ⟨found, hfound⟩
  subst found
  step with vec_index_given store.types function.signature signature hs as ⟨found, hfound⟩
  subst found
  rfl

/-- A foreign function address rejects before either function or type indexing. -/
theorem func_type_wrong_store {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (func : runtime.FuncAddr)
    (foreign : func.store ≠ store.id) :
    runtime.store.Store.func_type memory store func = .ok (.Err .WrongStore) := by
  simp only [runtime.store.Store.func_type, runtime.store.Store.check, if_neg foreign,
    bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, bind_tc_ok]

variable {M P F A : Type}
  (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
  (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
  (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
  (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)

/-- Any error from the checked signature lookup is returned unchanged. -/
theorem invoke_signature_rejection (error : runtime.ExecError)
    (lookup : runtime.store.Store.func_type memory store func = .ok (.Err error)) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err error, exec, store, platform, results) := by
  simp [runtime.interp.invoke_with, lookup, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from, lift, bind_ok]

/-- Foreign function handles reject before any index access or callback. -/
theorem invoke_wrong_store (foreign : func.store ≠ store.id) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results =
      .ok (.Err .WrongStore, exec, store, platform, results) := by
  apply invoke_signature_rejection memory hooks floats allocator exec store platform func args results .WrongStore
  simp [runtime.store.Store.func_type, runtime.store.Store.check, foreign,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Interp

end

/-! ## Divergence -/

section

/-!
Argument checking returns normally, so a divergent public invocation must have passed its actual argument check.

Main declarations: `invoke_divergent_arguments`. A direct consumer is `Integration.Instantiation.InstantiateSourceOrigin`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Argument checking returns normally, so a divergent public invocation
must have passed its actual argument check. -/
theorem invoke_divergent_arguments {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div) :
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) := by
  obtain ⟨answer, checked, decision⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  cases answer with
  | Ok unit => cases unit; exact checked
  | Err error =>
    obtain ⟨found, lookup, same⟩ := WP.spec_imp_exists
      (func_type_lookup memory store address function signature owner hf hs)
    subst found
    simp [runtime.interp.invoke_with, lookup, checked, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at divergent
end Itasca.Runtime.Interp

end

/-! ## ReadbackOwnership -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

@[step] theorem read_results_loop_owned {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.wasm_types.ValueType) (values : List val)
    (typed : types.val.map sourceType = values.map Compiler.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values)
    (bound : index.val ≤ values.length)
    (position : slot.val = Compiler.offset (values.map Compiler.valueType) index.val)
    (prior : results.val.map sourceValue = values.take index.val)
    (priorOwned : ∀ value ∈ results.val, OwnedBy store.id value) :
    runtime.interp.invoke_with_loop2 words store results index slot types ⦃ (afterStore, after) =>
      afterStore = store ∧ after.val.map sourceValue = values ∧
        (∀ value ∈ after.val, OwnedBy store.id value) ⦄ := by
  have lengths : types.length = values.length := by
    have h := congrArg List.length typed
    simpa using h
  unfold runtime.interp.invoke_with_loop2
  apply loop.spec_decr_nat (fun p => values.length - p.2.1.val)
    (fun p => p.2.1.val ≤ values.length ∧
      p.2.2.val = Compiler.offset (values.map Compiler.valueType) p.2.1.val ∧
      p.1.val.map sourceValue = values.take p.2.1.val ∧
      (∀ value ∈ p.1.val, OwnedBy store.id value))
  · rintro ⟨current, i, offset⟩ ⟨hi, hoffset, hprior, howners⟩
    dsimp only at hi hoffset hprior
    unfold runtime.interp.invoke_with_loop2.body
    dsimp only
    split
    · have hib : i.val < values.length := by scalar_tac
      have hit : i.val < types.val.length := by change i.val < types.length; omega
      let value := values[i.val]
      have hlookup : values[i.val]? = some value := by simp [value, List.getElem?_eq_getElem hib]
      have member : value ∈ values := List.getElem_mem hib
      step as ⟨ty, hty⟩
      have htype : sourceType ty = Compiler.valueType value := by
        have h := congrArg (fun xs => xs[i.val]?) typed
        simpa [List.getElem?_eq_getElem hit, hlookup, ← hty] using h
      have hrep : WordsAt (alloc.vec.Vec.deref words).val offset.val (Compiler.encodeValue value) := by
        have h := represented.lookup hlookup
        simpa [alloc.vec.Vec.deref, hoffset] using h
      obtain ⟨decoded,decodeActual,hraw,hdecoded⟩ := WP.spec_imp_exists
        (decode_slot_value (alloc.vec.Vec.deref words) offset ty store.id value
          (wellFormed value member) htype hrep (fits value member))
      have howner := decode_slot_owned_of_ok (alloc.vec.Vec.deref words) offset ty store.id decoded decodeActual
      rw [decodeActual,bind_ok]
      have hcurrent : current.length = i.val := by
        have h := congrArg List.length hprior
        simpa [List.length_take, Nat.min_eq_left hi] using h
      step as ⟨after, hafter⟩
      step with width_spec ty as ⟨width, hwidth⟩
      have hnextOffset : Compiler.offset (values.map Compiler.valueType) (i.val + 1) =
          offset.val + Compiler.width (sourceType ty) := by
        rw [hoffset]
        simp [Compiler.offset, List.take_add_one, hlookup, Compiler.slots_append, Compiler.slots, ← htype]
      have hcapacity : offset.val + Compiler.width (sourceType ty) ≤ words.length := by
        have hpositive := Compiler.width_positive (sourceType ty)
        have hlen : (Compiler.encodeValue value).length = Compiler.width (sourceType ty) := by
          rw [Compiler.encode_value_length, ← htype]
        have last := hrep ((Compiler.encodeValue value).length - 1) (by omega)
        simp only [alloc.vec.Vec.deref, Slice.from_val] at last
        change offset.val + Compiler.width (sourceType ty) ≤ words.val.length
        omega
      step as ⟨widthSize, hwidthSize⟩
      step as ⟨nextSlot, hnextSlot⟩
      step as ⟨next, hnext⟩
      refine ⟨by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
      · rw [hnext, hnextOffset]
        scalar_tac
      · rw [hnext, List.take_add_one, hlookup]
        simp [hafter, hprior, hdecoded, value]
      · intro value member
        rw [hafter] at member
        rcases List.mem_append.mp member with old | fresh
        · exact howners value old
        · simp only [List.mem_singleton] at fresh
          subst value
          exact howner
    · have he : i.val = values.length := by scalar_tac
      exact ⟨rfl, by simpa [he] using hprior,howners⟩
  · exact ⟨bound, position, prior,priorOwned⟩


/-- The actual result-copy loop returns precisely the represented source
results and leaves the store unchanged. -/
@[step] theorem read_results_owned {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (types : alloc.vec.Vec Itasca.wasm_types.ValueType) (values : List val)
    (empty : results.val = [])
    (typed : types.val.map sourceType = values.map Compiler.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values) :
    runtime.interp.invoke_with_loop2 words store results 0#usize 0#usize types
      ⦃ (afterStore, after) => afterStore = store ∧ after.val.map sourceValue = values ∧
        (∀ value ∈ after.val, OwnedBy store.id value) ⦄ := by
  apply read_results_loop_owned words store results 0#usize 0#usize types values typed wellFormed fits represented
  · simp
  · simp [Compiler.offset, Compiler.slots]
  · simp [empty]
  · simp [empty]

end Itasca.Runtime.Interp

end

/-! ## ResourceCauses -/

section

/-!
Exact source-signature causes introduced by public invocation setup and result marshaling. These are separate from execution's frame requirements.

Main declarations: `InvocationResourceCause`. A direct consumer is `Interp.Invocation.MutableCauses`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact source-signature causes introduced by public invocation setup and
result marshaling. These are separate from execution's frame requirements. -/
def InvocationResourceCause {A M : Type} (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (signature : Itasca.wasm_types.FuncType) (results : alloc.vec.Vec runtime.Value) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val <
      max (typeSlots signature.params.val) (typeSlots signature.results.val)
  | .Exhausted .Allocation =>
      (∃ n : Usize, n.val ≤ max (typeSlots signature.params.val) (typeSlots signature.results.val) ∧
        allocator.reserve exec.slots n = .ok (false, exec.slots)) ∨
      (∃ n : Usize, n.val = signature.results.length - results.length ∧
        allocator.reserve results n = .ok (false, results))
  | _ => False

end Itasca.Runtime.Interp

end

/-! ## PrefixCauses -/

section

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
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
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
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
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

end

/-! ## PrefixDivergence -/

section

/-!
Public-wrapper divergence must come from an entered interpreter loop; metadata prefixes permit host callbacks to publish new functions.

Main declarations: `invoke_prefix_divergent_entry`. A direct consumer is `Integration.Invocation.DefinedDivergence`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

private theorem total_of_nondivergent {α : Type} {run : Result α} {post : α → Prop}
    (safe : WP.dspec run post) (nondivergent : run ≠ .div) : WP.spec run post := by
  cases safe with
  | ret satisfied => exact .ret satisfied
  | div => exact False.elim (nondivergent rfl)

/-- Public-wrapper divergence must come from an entered interpreter loop;
metadata prefixes permit host callbacks to publish new functions. -/
theorem invoke_prefix_divergent_entry {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store=store.id)
    (hf : store.funcs.val[address.index.val]?=some function)
    (hs : store.types.val[function.signature.val]?=some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params)=.ok (.Ok ()))
    (owned : ∀value∈args.val,ValueOwnedFits store.id value)
    (entry : runtime.store.Store M → runtime.interp.Execution → Prop)
    (called : ∀prepared p,prepared.store=store.id → prepared.frames.val=[] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      runtime.interp.call memory hooks floats allocator prepared store p address 0#usize ⦃ out =>
        out.1=.Ok () → entry out.2.2.1 out.2.1 ⦄)
    (executed : ∀after prepared p,entry after prepared →
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())
        ⦃ (_,words,_,_,_,afterStore,_,status) => FrameStorePrefix store afterStore ∧
          (status=.Ok () → ∃values,
            signature.results.val.map sourceType=values.map Compiler.valueType ∧
            (∀value∈values,wf_val value) ∧ (∀value∈values,ResultIndexFits value) ∧
            ValuesAt words.val 0 values) ⦄div)
    (diverges : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    ∃after prepared p,entry after prepared ∧
      runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ())=.div := by
  classical
  by_contra absent
  have total : WP.spec
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out=>True ∧ (out.1=.Ok () → True) ∧ (∀error,out.1=.Err error → True)) := by
    refine (invoke_with_prefix_causes_composition_mode memory hooks floats allocator False allocation exec store platform
      address function signature args results owner hf hs accepted owned entry (fun _=>True) trivial (fun _ _=>True)
      (fun _ _=>True) (by intros; trivial) ?_ ?_).spec
    · intro prepared p identity empty arguments
      apply DivSpec.of_spec
      apply WP.spec_mono (called prepared p identity empty arguments)
      intro out post
      exact ⟨trivial,post,by intros; trivial⟩
    · intro after prepared p entered
      have safe := executed after prepared p entered
      have normal : WP.spec
          (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ()))
          (fun (_,words,_,_,_,afterStore,_,status)=> FrameStorePrefix store afterStore ∧
            (status=.Ok () → ∃values,signature.results.val.map sourceType=values.map Compiler.valueType ∧
              (∀value∈values,wf_val value) ∧ (∀value∈values,ResultIndexFits value) ∧ ValuesAt words.val 0 values)) := by
        apply total_of_nondivergent safe
        intro divergent
        exact absent ⟨after,prepared,p,entered,divergent⟩
      apply DivSpec.of_spec
      apply WP.spec_mono normal
      rintro out ⟨metadata,success⟩
      refine ⟨metadata,trivial,?_,by intros; trivial⟩
      intro ok
      obtain ⟨values,tags,wf,fits,represented⟩ := success ok
      exact ⟨values,tags,wf,fits,represented,trivial⟩
  rw [diverges] at total
  exact WP.spec_div.mp total
end Itasca.Runtime.Interp

end

/-! ## MutableCauses -/

section

/-!
Runtime error kinds justified by invocation setup and result-marshaling resource causes.

Main declarations: `InvocationResourceCause.kind`. A direct consumer is `Integration.Api.InvocationEntryResources`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem InvocationResourceCause.kind {A M : Type} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {signature : Itasca.wasm_types.FuncType}
    {results : alloc.vec.Vec runtime.Value} {error : runtime.ExecError}
    (cause : InvocationResourceCause allocator exec store signature results error) :
    error=.Exhausted .Values ∨ error=.Exhausted .Allocation := by
  cases error <;> simp only [InvocationResourceCause] at cause
  all_goals try contradiction
  case Exhausted reason => cases reason <;> simp_all [InvocationResourceCause]

end Itasca.Runtime.Interp

end

/-! ## LoopRecording -/

section

/-!
Proof-only recording of interpreter-loop events, with erasure back to the extracted loop.

Main declarations: `recordedInvokeLoop` and `recorded_invoke_loop_erase`. A direct consumer is `Interp.Invocation.LoopRecordingFacts`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

abbrev InvokeLoopState (M P : Type) := runtime.interp.Execution × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError
abbrev InvokeLoopResult (M P : Type) := Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame ×
  alloc.vec.Vec runtime.Value × alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError

/-- Only continuing body results perform a dispatch. The stopping guard and
its status check contribute no host event. -/
def invokeLoopEvents {M P : Type} (before : InvokeLoopState M P)
    (out : ControlFlow (InvokeLoopState M P) (InvokeLoopResult M P)) : List HostEvent :=
  match out with
  | .cont (exec,store,platform,status) => stepHostEvents before.1 before.2.1 (status,exec,store,platform)
  | .done _ => []

def recordedInvokeLoop {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    Result (InvokeLoopResult M P × List HostEvent) :=
  Platform.Recording.loop
    (fun (exec,store,platform,status) => runtime.interp.invoke_with_loop1.body memory hooks floats allocator exec store platform status)
    invokeLoopEvents (exec,store,platform,status) prior

theorem recorded_invoke_loop_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    (do let (out,_) ← recordedInvokeLoop memory hooks floats allocator exec store platform status prior; Result.ok out) =
      runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status := by
  exact Platform.Recording.loop_erase _ _ _ _
end Itasca.Runtime.Interp

end

/-! ## LoopRecordingFacts -/

section

/-!
One-step and stopped-case equations for the recorded invocation loop.

Main declarations: `recorded_invoke_loop_step` and `recorded_invoke_loop_stopped`. A direct consumer is `Integration.Invocation.HostResources`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem recorded_invoke_loop_step {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {status : core.result.Result Unit runtime.ExecError} {nextExec : runtime.interp.Execution}
    {nextStore : runtime.store.Store M} {nextPlatform : P}
    (returned : runtime.interp.step memory hooks floats allocator exec store platform=.ok (status,nextExec,nextStore,nextPlatform))
    (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator exec store platform (.Ok ()) prior =
      recordedInvokeLoop memory hooks floats allocator nextExec nextStore nextPlatform status
        (prior++stepHostEvents exec store (status,nextExec,nextStore,nextPlatform)) := by
  have active : ActiveExecution (exec,store,platform,.Ok ()) := ⟨step_returned_active memory hooks floats allocator returned,rfl⟩
  change Platform.Recording.loop (executionBody memory hooks floats allocator) invokeLoopEvents (exec,store,platform,.Ok ()) prior = _
  unfold Platform.Recording.loop
  rw [loop.eq_def]
  simp only [Platform.Recording.loopBody,execution_body_active memory hooks floats allocator _ active,returned,bind_ok,Std.uncurry,invokeLoopEvents]
  rfl

theorem recorded_invoke_loop_stopped {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (state : ExecutionState M P) (stopped : ¬ActiveExecution state) (prior : List HostEvent) :
    recordedInvokeLoop memory hooks floats allocator state.1 state.2.1 state.2.2.1 state.2.2.2 prior =
      .ok (finishExecution state,prior) := by
  change Platform.Recording.loop (executionBody memory hooks floats allocator) invokeLoopEvents state prior = _
  unfold Platform.Recording.loop
  rw [loop.eq_def]
  simp only [Platform.Recording.loopBody,execution_body_stopped memory hooks floats allocator state stopped,bind_ok,invokeLoopEvents,List.append_nil]
end Itasca.Runtime.Interp

end

/-! ## Recording -/

section

/-!
Proof-only public invocation recording and its exact returned event log.

Main declarations: `InvocationResult` and `recordedInvokeWith`. A direct consumer is `Interp.Invocation.RecordedChecks`.
-/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

abbrev InvocationResult (M P : Type) := core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
  runtime.store.Store M × P × alloc.vec.Vec runtime.Value

/-- Transparent writer instrumentation of the extracted public invocation.
Only the initial call and dispatch loop append events. All argument checks,
preparation errors and result readback follow the original control flow. -/
def recordedInvokeWith {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) : Result (InvocationResult M P × List HostEvent) := do
  let r ← runtime.store.Store.func_type memory store func
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val.params
    let r1 ←
      runtime.interp.check_values memory store args s
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 := alloc.vec.Vec.deref val.params
      let r2 ← runtime.interp.type_slots s1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s2 := alloc.vec.Vec.deref val.results
        let r3 ← runtime.interp.type_slots s2
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let needed ← lift (core.cmp.impls.OrdUsize.max val1 val2)
          let (r4, exec1) ←
            runtime.interp.Execution.ensure allocator exec needed
              store.limits.max_values
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let v ← runtime.clear exec1.frames
            let v1 ←
              runtime.interp.invoke_with_loop0 exec1.slots args val.params 0#usize
                0#usize
            let ((r5, exec2, store1, platform1),callTrace) ←
              recordedCall memory hooks
                floats allocator
                { exec1 with store := store.id, slots := v1, frames := v } store platform func 0#usize prior
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let ((i, v5, v6, v7, v8, store2, platform2, status),loopTrace) ←
                recordedInvokeLoop memory
                  hooks floats allocator
                  exec2 store1 platform1 (core.result.Result.Ok ()) callTrace
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch status
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ←
                  runtime.store.Store.func_type memory store2
                    func
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let i1 := alloc.vec.Vec.len val3.results
                  let i2 := alloc.vec.Vec.len results
                  let i3 ← lift (core.num.Usize.saturating_sub i1 i2)
                  let (r7, results1) ←
                    runtime.reserve allocator results i3
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let results2 ← runtime.clear results1
                    let (store3, results3) ←
                      runtime.interp.invoke_with_loop2 v5 store2 results2
                        0#usize 0#usize val3.results
                    Result.ok ((core.result.Result.Ok (),
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store3, platform2, results3),loopTrace)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r8 ←
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        Unit (core.convert.FromSame
                        _root_.Itasca.runtime.ExecError) residual
                    Result.ok ((r8,
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store2, platform2, results1),loopTrace)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r7 ←
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      Unit (core.convert.FromSame
                      _root_.Itasca.runtime.ExecError) residual
                  Result.ok ((r7,
                    {
                      store := i,
                      slots := v5,
                      frames := v6,
                      host_args := v7,
                      host_results := v8
                    }, store2, platform2, results),loopTrace)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r6 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                    residual
                Result.ok ((r6,
                  {
                    store := i,
                    slots := v5,
                    frames := v6,
                    host_args := v7,
                    host_results := v8
                  }, store2, platform2, results),loopTrace)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                  residual
              Result.ok ((r6, exec2, store1, platform1, results),callTrace)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
                residual
            Result.ok ((r5, exec1, store, platform, results),prior)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError)
              residual
          Result.ok ((r4, exec, store, platform, results),prior)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
        Result.ok ((r3, exec, store, platform, results),prior)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
      Result.ok ((r2, exec, store, platform, results),prior)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.runtime.ExecError) residual
    Result.ok ((r1, exec, store, platform, results),prior)

end Itasca.Runtime.Interp

end
