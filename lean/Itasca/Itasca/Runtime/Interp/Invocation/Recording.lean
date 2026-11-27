import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Interp.Relations.StepActive
import Itasca.Runtime.Interp.Relations.TypedOperands
import Itasca.Runtime.Interp.Relations.SlotsAndDefaults
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings
import Itasca.Support.Translation
import Itasca.Runtime.Platform.Laws
import Itasca.Runtime.Interp.Relations.StackPreservation

/-!
Proofs for Runtime / Interp / Invocation.

This module collects CallRecording, Recording.
Each section documents its contracts and consumers.
-/

/-! ## CallRecording -/

section

/-!
# Recorded call events

Returning recorded calls retain the concrete call result. Host calls contribute their direct event, while Wasm calls retain the appropriate call-event behavior.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

theorem recorded_call_returned {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (prior : List HostEvent) (out) (trace : List HostEvent) :
    recordedCall memory hooks floats allocator exec store platform address base prior = .ok (out,trace) ↔
      runtime.interp.call memory hooks floats allocator exec store platform address base = .ok out ∧
      trace = prior ++ callHostEvents store address out :=
  Platform.Recording.returned _ _ _ _ _

theorem call_host_events_host {M P : Type} {store : runtime.store.Store M} {address : runtime.FuncAddr}
    {function : runtime.store.FuncInst} {identity : U64}
    (found : store.funcs.val[address.index.val]?=some function) (host : function.code=.Host identity)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) :
    callHostEvents store address out = hostCallEvents address out := by
  simp only [callHostEvents,found,host]

theorem call_host_events_wasm {M P : Type} {store : runtime.store.Store M} {address : runtime.FuncAddr}
    {function : runtime.store.FuncInst} {instanceIndex functionIndex : Usize}
    (found : store.funcs.val[address.index.val]?=some function) (defined : function.code=.Wasm instanceIndex functionIndex)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) :
    callHostEvents store address out = [] := by
  simp only [callHostEvents,found,defined]
end Itasca.Interp

end

/-! ## Recording -/

section

/-!
Proofs for Runtime / Interp / Invocation.

This module collects Recording, RecordingErasure.
Each section documents its contracts and consumers.
-/

/-! ## Recording -/

section

open Itasca.Representation

/-!
# Recording

Transparent invocation recording agrees with checks, loops and result readback. Prefix resource causes and divergence preserve the actual host-event history.
-/

/-! ## Checks -/

section

/-! Public invocation rejection before execution begins. These conclusions
preserve execution state, store, platform, and the caller's result vector. -/
namespace Itasca.Interp
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

end Itasca.Interp

end

/-! ## Divergence -/

section

/-!
Argument checking returns normally, so a divergent public invocation must have passed its actual argument check.

Main declarations: `invoke_divergent_arguments`.
-/

namespace Itasca.Interp
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
end Itasca.Interp

end

/-! ## ReadbackOwnership -/

section

namespace Itasca.Interp
open Aeneas Aeneas.Std

@[step] theorem read_results_loop_owned {M : Type} (words : alloc.vec.Vec U64)
    (store : runtime.store.Store M) (results : alloc.vec.Vec runtime.Value)
    (index slot : Usize) (types : alloc.vec.Vec Itasca.wasm_types.ValueType) (values : List val)
    (typed : types.val.map Itasca.Translation.valueType = values.map Representation.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values)
    (bound : index.val ≤ values.length)
    (position : slot.val = Representation.offset (values.map Representation.valueType) index.val)
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
      p.2.2.val = Representation.offset (values.map Representation.valueType) p.2.1.val ∧
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
      have htype : Itasca.Translation.valueType ty = Representation.valueType value := by
        have h := congrArg (fun xs => xs[i.val]?) typed
        simpa [List.getElem?_eq_getElem hit, hlookup, ← hty] using h
      have hrep : WordsAt (alloc.vec.Vec.deref words).val offset.val (Representation.encodeValue value) := by
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
      have hnextOffset : Representation.offset (values.map Representation.valueType) (i.val + 1) =
          offset.val + Representation.width (Itasca.Translation.valueType ty) := by
        rw [hoffset]
        simp [Representation.offset, List.take_add_one, hlookup, Representation.slots_append, Representation.slots, ← htype]
      have hcapacity : offset.val + Representation.width (Itasca.Translation.valueType ty) ≤ words.length := by
        have hpositive := Representation.width_positive (Itasca.Translation.valueType ty)
        have hlen : (Representation.encodeValue value).length = Representation.width (Itasca.Translation.valueType ty) := by
          rw [Representation.encode_value_length, ← htype]
        have last := hrep ((Representation.encodeValue value).length - 1) (by omega)
        simp only [alloc.vec.Vec.deref, Slice.from_val] at last
        change offset.val + Representation.width (Itasca.Translation.valueType ty) ≤ words.val.length
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
    (typed : types.val.map Itasca.Translation.valueType = values.map Representation.valueType)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt words.val 0 values) :
    runtime.interp.invoke_with_loop2 words store results 0#usize 0#usize types
      ⦃ (afterStore, after) => afterStore = store ∧ after.val.map sourceValue = values ∧
        (∀ value ∈ after.val, OwnedBy store.id value) ⦄ := by
  apply read_results_loop_owned words store results 0#usize 0#usize types values typed wellFormed fits represented
  · simp
  · simp [Representation.offset, Representation.slots]
  · simp [empty]
  · simp [empty]

end Itasca.Interp

end

/-! ## ResourceCauses -/

section

/-!
Exact source-signature causes introduced by public invocation setup and result marshaling. These are separate from execution's frame requirements.

Main declarations: `InvocationResourceCause`.
-/

namespace Itasca.Interp
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

end Itasca.Interp

end

/-! ## PrefixCauses -/

section

/-!
Invocation permits store extension during entry and execution, retaining the original function and signature through checked raw metadata prefixes.

Main declarations: `invoke_with_prefix_owned_causes_composition_mode` and `invoke_with_prefix_causes_composition_mode`.
-/

namespace Itasca.Interp
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
      Computation.DivSpec cause (runtime.interp.call memory hooks floats allocator prepared store p address 0#usize) fun out =>
        retained out.2.2.1 ∧ (out.1 = .Ok () → entry out.2.2.1 out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error))
    (executed : ∀ enteredStore prepared p, entry enteredStore prepared →
      Computation.DivSpec cause
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared enteredStore p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          Store.MetadataExtended store afterStore ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map Itasca.Translation.valueType = values.map Representation.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    Computation.DivSpec cause
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
          step with runtime.clear.spec grown.frames as ⟨frames, empty⟩
          generalize sameWords : grown.slots = words
          generalize sameArgs : grown.host_args = hostArgs
          generalize sameResults : grown.host_results = hostResults
          have wordsEq := sameWords.symm
          have argsEq := sameArgs.symm
          have resultsEq := sameResults.symm
          have capacity : (Representation.encodeValues (args.val.map sourceValue)).length ≤ words.length := by
            have length : grown.slots.length = exec.slots.length + ((core.cmp.impls.OrdUsize.max params returns).val - exec.slots.length) := by
              change grown.slots.val.length = _
              rw [growth.2.1, List.length_append, List.length_replicate]
            rw [wordsEq, Representation.encode_values_length]
            simp only [alloc.vec.Vec.deref, typeSlots, Slice.from_val] at paramCount
            have typeEq : (args.val.map sourceValue).map Representation.valueType = signature.params.val.map Itasca.Translation.valueType := by
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
                step with runtime.clear.spec results as ⟨emptyResults, empty⟩
                step with read_results_owned finalWords finalStore emptyResults signature.results values empty types wellFormed fits represented
                  as ⟨returnedStore, returnedResults, sameStore, sameResults, resultOwners⟩
                subst returnedStore
                try simp only [Computation.DivSpec.ok_iff]
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
      Computation.DivSpec cause (runtime.interp.call memory hooks floats allocator prepared store p address 0#usize) fun out =>
        retained out.2.2.1 ∧ (out.1 = .Ok () → entry out.2.2.1 out.2.1) ∧
          (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error))
    (executed : ∀ enteredStore prepared p, entry enteredStore prepared →
      Computation.DivSpec cause
        (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared enteredStore p (.Ok ()))
        (fun (_, words, _, _, _, afterStore, _, status) =>
          Store.MetadataExtended store afterStore ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map Itasca.Translation.valueType = values.map Representation.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values) ∧
          (∀ error, status = .Err error → errorProperty afterStore error))) :
    Computation.DivSpec cause
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results)
      (fun out => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error)) := by
  apply Computation.DivSpec.mono (invoke_with_prefix_owned_causes_composition_mode memory hooks floats allocator cause allocation
    exec store platform address function signature args results owner hf hs accepted owned entry retained initial
    property errorProperty (fun error cause => resourceError store error cause)
    (fun after values kept satisfied refused => resourceError after _ (Or.inr refused)) called executed)
  rintro out ⟨kept,success,errors⟩
  exact ⟨kept,fun accepted => (success accepted).1,errors⟩

end Itasca.Interp

end

/-! ## PrefixDivergence -/

section

/-!
Public-wrapper divergence must come from an entered interpreter loop; metadata prefixes permit host callbacks to publish new functions.

Main declarations: `invoke_prefix_divergent_entry`.
-/

namespace Itasca.Interp
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
        ⦃ (_,words,_,_,_,afterStore,_,status) => Store.MetadataExtended store afterStore ∧
          (status=.Ok () → ∃values,
            signature.results.val.map Itasca.Translation.valueType=values.map Representation.valueType ∧
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
      apply Computation.DivSpec.of_spec
      apply WP.spec_mono (called prepared p identity empty arguments)
      intro out post
      exact ⟨trivial,post,by intros; trivial⟩
    · intro after prepared p entered
      have safe := executed after prepared p entered
      have normal : WP.spec
          (runtime.interp.invoke_with_loop1 memory hooks floats allocator prepared after p (.Ok ()))
          (fun (_,words,_,_,_,afterStore,_,status)=> Store.MetadataExtended store afterStore ∧
            (status=.Ok () → ∃values,signature.results.val.map Itasca.Translation.valueType=values.map Representation.valueType ∧
              (∀value∈values,wf_val value) ∧ (∀value∈values,ResultIndexFits value) ∧ ValuesAt words.val 0 values)) := by
        apply total_of_nondivergent safe
        intro divergent
        exact absent ⟨after,prepared,p,entered,divergent⟩
      apply Computation.DivSpec.of_spec
      apply WP.spec_mono normal
      rintro out ⟨metadata,success⟩
      refine ⟨metadata,trivial,?_,by intros; trivial⟩
      intro ok
      obtain ⟨values,tags,wf,fits,represented⟩ := success ok
      exact ⟨values,tags,wf,fits,represented,trivial⟩
  rw [diverges] at total
  exact WP.spec_div.mp total
end Itasca.Interp

end

/-! ## MutableCauses -/

section

/-!
Runtime error kinds justified by invocation setup and result-marshaling resource causes.

Main declarations: `InvocationResourceCause.kind`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std

theorem InvocationResourceCause.kind {A M : Type} {allocator : runtime.platform.Alloc A}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {signature : Itasca.wasm_types.FuncType}
    {results : alloc.vec.Vec runtime.Value} {error : runtime.ExecError}
    (cause : InvocationResourceCause allocator exec store signature results error) :
    error=.Exhausted .Values ∨ error=.Exhausted .Allocation := by
  cases error <;> simp only [InvocationResourceCause] at cause
  all_goals try contradiction
  case Exhausted reason => cases reason <;> simp_all [InvocationResourceCause]

end Itasca.Interp

end

/-! ## LoopRecording -/

section

/-!
Proof-only recording of interpreter-loop events, with erasure back to the extracted loop.

Main declarations: `recordedInvokeLoop` and `recorded_invoke_loop_erase`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

theorem recorded_invoke_loop_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (status : core.result.Result Unit runtime.ExecError) (prior : List HostEvent) :
    (do let (out,_) ← recordedInvokeLoop memory hooks floats allocator exec store platform status prior; Result.ok out) =
      runtime.interp.invoke_with_loop1 memory hooks floats allocator exec store platform status := by
  exact Platform.Recording.loop_erase _ _ _ _
end Itasca.Interp

end

/-! ## LoopRecordingFacts -/

section

/-!
One-step and stopped-case equations for the recorded invocation loop.

Main declarations: `recorded_invoke_loop_step` and `recorded_invoke_loop_stopped`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

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
end Itasca.Interp

end

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly Itasca.Platform

/-- Returning loop histories concatenate the actual callback segments in order.
The invariant concerns only returned executions; it assumes no fuel bound. -/
theorem recorded_loop_observations {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (steps : Observation.Step memory hooks floats allocator)
    (origin : List (HostObservation M))
    (state : InvokeLoopState M (P × List (HostObservation M))) (events : List HostEvent)
    (initial : ObservationExtension origin state.2.2.1.2 events)
    (out : InvokeLoopResult M (P × List (HostObservation M)) × List HostEvent)
    (run : recordedInvokeLoop memory (observing hooks) floats allocator state.1 state.2.1
      state.2.2.1 state.2.2.2 events = .ok out) :
    ObservationExtension origin out.1.2.2.2.2.2.2.1.2 out.2 := by
  apply loop_returned_invariant
    (Recording.loopBody (executionBody memory (observing hooks) floats allocator) invokeLoopEvents)
    (fun s => ObservationExtension origin s.1.2.2.1.2 s.2)
    (fun answer => ObservationExtension origin answer.1.2.2.2.2.2.2.1.2 answer.2)
    ?_ (state,events) initial out run
  rintro ⟨⟨exec,store,⟨platform,prior⟩,status⟩,events⟩ result held returned
  by_cases active : ActiveExecution (exec,store,(platform,prior),status)
  · simp only [Recording.loopBody,execution_body_active memory (observing hooks) floats allocator _ active,
      Std.bind_assoc] at returned
    obtain ⟨⟨status,finished,after,next⟩,stepped,returned⟩ := Computation.bind_ok_inv _ _ _ returned
    simp only [Std.uncurry,bind_ok,invokeLoopEvents,Result.ok.injEq] at returned
    subst result
    exact held.append (steps exec store platform prior (status,finished,after,next) stepped)
  · simp only [Recording.loopBody,execution_body_stopped memory (observing hooks) floats allocator _ active,
      bind_ok,invokeLoopEvents,List.append_nil,Result.ok.injEq] at returned
    subst result
    exact held
end Itasca.Interp

end

/-! ## RecordingErasure -/

section

open Itasca.Representation

/-! ## RecordedPrefix -/

section

/-!
Invocation permits store extension during entry and execution, retaining the original function and signature through checked raw metadata prefixes.

Main declarations: `recorded_invoke_with_prefix_owned_causes_composition_mode`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

/-- Invocation permits store extension during entry and execution, retaining the
original function and signature through checked raw metadata prefixes. -/
theorem recorded_invoke_with_prefix_owned_causes_composition_mode {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (cause : Prop)
    (allocation : Platform.AllocCorrect allocator)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value) (prior : List HostEvent)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, ValueOwnedFits store.id value)
    (entry : runtime.store.Store M → runtime.interp.Execution → List HostEvent → Prop)
    (retained : runtime.store.Store M → Prop) (initial : retained store)
    (property : runtime.store.Store M → List val → List HostEvent → Prop)
    (errorProperty : runtime.store.Store M → runtime.ExecError → List HostEvent → Prop)
    (resourceError : ∀ error, InvocationResourceCause allocator exec store signature results error → errorProperty store error prior)
    (readbackError : ∀ after values trace, retained after → property after values trace →
      (∃ n : Usize, n.val = signature.results.length - results.length ∧
        allocator.reserve results n = .ok (false,results)) → errorProperty after (.Exhausted .Allocation) trace)
    (called : ∀ prepared p, prepared.store = store.id → prepared.frames.val = [] →
      ValuesAt prepared.slots.val 0 (args.val.map sourceValue) →
      Computation.DivSpec cause (recordedCall memory hooks floats allocator prepared store p address 0#usize prior) fun (out,trace) =>
        retained out.2.2.1 ∧ (out.1 = .Ok () → entry out.2.2.1 out.2.1 trace) ∧
          (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error trace))
    (executed : ∀ enteredStore prepared p entryTrace, entry enteredStore prepared entryTrace →
      Computation.DivSpec cause
        (recordedInvokeLoop memory hooks floats allocator prepared enteredStore p (.Ok ()) entryTrace)
        (fun ((_, words, _, _, _, afterStore, _, status),trace) =>
          Store.MetadataExtended store afterStore ∧ retained afterStore ∧
          (status = .Ok () → ∃ values,
            signature.results.val.map Itasca.Translation.valueType = values.map Representation.valueType ∧
            (∀ value ∈ values, wf_val value) ∧
            (∀ value ∈ values, ResultIndexFits value) ∧
            ValuesAt words.val 0 values ∧ property afterStore values trace) ∧
          (∀ error, status = .Err error → errorProperty afterStore error trace))) :
    Computation.DivSpec cause
      (recordedInvokeWith memory hooks floats allocator exec store platform address args results prior)
      (fun (out,trace) => retained out.2.2.1 ∧ (out.1 = .Ok () → property out.2.2.1 (out.2.2.2.2.val.map sourceValue) trace ∧
        (∀ value ∈ out.2.2.2.2.val, OwnedBy out.2.2.1.id value)) ∧
        (∀ error, out.1 = .Err error → errorProperty out.2.2.1 error trace)) := by
  have tags : signature.params.val = args.val.map rawType := by
    have checked := check_values_accepts_iff memory store args (alloc.vec.Vec.deref signature.params)
    rw [accepted] at checked
    simp only [WP.spec_ok] at checked
    have matched : List.Forall₂ (ArgumentMatches store.id) args.val signature.params.val := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using checked.mp trivial
    exact argument_matches_rawtypes matched
  all_goals
    unfold recordedInvokeWith
    step with func_type_lookup memory store address function signature owner hf hs as ⟨found, same⟩
    subst found
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [accepted]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step with type_slots_effect (alloc.vec.Vec.deref signature.params) as ⟨params, paramCount⟩
    cases params with
    | Err error =>
      obtain ⟨rfl, overflow⟩ := paramCount
      have cause : errorProperty store (.Exhausted .Values) prior := resourceError _ (by
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
        have cause : errorProperty store (.Exhausted .Values) prior := resourceError _ (by
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
          have allowed : errorProperty store error prior := by
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
          step with runtime.clear.spec grown.frames as ⟨frames, empty⟩
          generalize sameWords : grown.slots = words
          generalize sameArgs : grown.host_args = hostArgs
          generalize sameResults : grown.host_results = hostResults
          have wordsEq := sameWords.symm
          have argsEq := sameArgs.symm
          have resultsEq := sameResults.symm
          have capacity : (Representation.encodeValues (args.val.map sourceValue)).length ≤ words.length := by
            have length : grown.slots.length = exec.slots.length + ((core.cmp.impls.OrdUsize.max params returns).val - exec.slots.length) := by
              change grown.slots.val.length = _
              rw [growth.2.1, List.length_append, List.length_replicate]
            rw [wordsEq, Representation.encode_values_length]
            simp only [alloc.vec.Vec.deref, typeSlots, Slice.from_val] at paramCount
            have typeEq : (args.val.map sourceValue).map Representation.valueType = signature.params.val.map Itasca.Translation.valueType := by
              rw [tags, List.map_map, List.map_map]
              congr 1
              funext value
              exact source_value_type value
            rw [typeEq]
            scalar_tac
          step with marshal_arguments words args signature.params store.id tags owned capacity
            as ⟨encoded, sameLength, represented⟩
          step with called ⟨store.id, encoded, frames, hostArgs, hostResults⟩ platform rfl empty represented
            as ⟨status,entered,calledStore,calledPlatform,callTrace,post⟩
          obtain ⟨calledRetained,enteredProof,callError⟩ := post
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, callError error rfl, calledRetained]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with executed calledStore entered calledPlatform callTrace (enteredProof rfl)
              as ⟨id,finalWords,finalFrames,finalArgs,finalHostResults,finalStore,finalPlatform,status,finalTrace,post⟩
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
                have cause : errorProperty finalStore (.Exhausted .Allocation) finalTrace := readbackError finalStore values finalTrace finalRetained satisfied
                  ⟨additional, by simp [additional, core.num.Usize.saturating_sub, saturating_sub_value], actualReserve⟩
                simp [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, cause, finalRetained]
              | true =>
                simp only [ite_true, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
                step with runtime.clear.spec results as ⟨emptyResults, empty⟩
                step with read_results_owned finalWords finalStore emptyResults signature.results values empty types wellFormed fits represented
                  as ⟨returnedStore, returnedResults, sameStore, sameResults, resultOwners⟩
                subst returnedStore
                try simp only [Computation.DivSpec.ok_iff]
                exact ⟨finalRetained, (fun _ => ⟨by simpa only [sameResults] using satisfied,resultOwners⟩), by intro error impossible; cases impossible⟩

end Itasca.Interp

end

/-! ## RecordedChecks -/

section

/-!
Lift an accepted-argument contract through the actual public checker. Rejection retains the exact unchanged execution, store, platform, and results.

Main declarations: `recorded_invoke_with_checked_outcome` and `recorded_invoke_wrong_store`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly

/-- Lift an accepted-argument contract through the actual public checker.
Rejection retains the exact unchanged execution, store, platform, and results. -/
theorem recorded_invoke_with_checked_outcome {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.wasm_types.FuncType) (args : Slice runtime.Value)
    (results : alloc.vec.Vec runtime.Value) (prior : List HostEvent)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (property : InvocationResult M P × List HostEvent → Prop)
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) →
      recordedInvokeWith memory hooks floats allocator exec store platform address args results prior ⦃ out => property out ⦄div) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results prior
      ⦃ out =>
        (∃ error, runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Err error) ∧
          out = ((.Err error,exec,store,platform,results),prior)) ∨
        (runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()) ∧ property out) ⦄div := by
  obtain ⟨answer,checked,decision⟩ := WP.spec_imp_exists
    (check_values_effect memory store args (alloc.vec.Vec.deref signature.params))
  cases answer with
  | Ok unit =>
    cases unit
    apply WP.dspec_mono (accepted checked)
    intro out post
    exact Or.inr ⟨checked,post⟩
  | Err error =>
    obtain ⟨found,lookup,same⟩ := WP.spec_imp_exists
      (func_type_lookup memory store address function signature owner hf hs)
    subst found
    have returned : recordedInvokeWith memory hooks floats allocator exec store platform address args results prior =
        .ok ((.Err error,exec,store,platform,results),prior) := by
      simp [recordedInvokeWith,lookup,checked,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    rw [returned]
    apply WP.dspec.ret
    exact Or.inl ⟨error,checked,rfl⟩

/-- A foreign initial handle is rejected without appending a host event. -/
theorem recorded_invoke_wrong_store {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) (foreign : address.store ≠ store.id) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results prior =
      .ok ((.Err .WrongStore,exec,store,platform,results),prior) := by
  simp [recordedInvokeWith,runtime.store.Store.func_type,runtime.store.Store.check,foreign,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Itasca.Interp

end

/-! ## RecordingErasure -/

section

/-!
Erasing the writer recovers the extracted invocation for arbitrary hooks and internal states, including failure and divergence.

Main declarations: `recorded_invoke_with_erase`.
-/

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly
/-- Erasing the writer recovers the extracted invocation for arbitrary hooks
and internal states, including failure and divergence. -/
theorem recorded_invoke_with_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) :
    (do let (out,_) ← recordedInvokeWith memory hooks floats allocator exec store platform func args results prior
        Result.ok out) = runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results := by
  unfold recordedInvokeWith runtime.interp.invoke_with
  simp only [recordedCall,Platform.Recording.run,Std.uncurry,Std.bind_assoc,bind_ok]
  repeat' first
    | rfl
    | (apply Platform.Recording.bind_erase_cont _ _ _ _ (recorded_invoke_loop_erase ..)
       intro answer trace
       rcases answer with ⟨id,words,frames,hostArgs,hostResults,after,host,status⟩
       simp only [Std.bind_assoc,bind_ok,Std.uncurry])
    | (apply congrArg (Std.bind _)
       funext answer)
    | (split <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])

end Itasca.Interp

end

/-! Callback observation preserves the extracted computation under erasure. -/

namespace Itasca.Interp
open Aeneas Aeneas.Std Itasca.Platform

/-- Observation commutes with the public invocation, including terminal
failure and divergence. The interpreter is the original extracted function. -/
theorem observing_invoke_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List (HostObservation M)) :
    (do let (result, nextExec, after, (next, _), returned) ←
          runtime.interp.invoke_with memory (observing hooks) floats allocator exec store
            (platform, prior) address args results
        Result.ok (result, nextExec, after, next, returned)) =
      runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results := by
  unfold runtime.interp.invoke_with
  simp only [Std.bind_assoc, Std.uncurry]
  repeat' first
    | rfl
    | (apply bind_project _ _ _ _ _ (observing_call_execution_erase ..)
       rintro ⟨result, nextExec, after, next, trace⟩
       simp only [Std.uncurry])
    | (apply bind_project _ _ _ _ _ (observing_invoke_loop_erase ..)
       rintro ⟨id, words, frames, hostArgs, hostResults, after, ⟨next, trace⟩, status⟩
       simp only [eraseLoopAnswer, Std.uncurry])
    | (apply congrArg (Std.bind _); funext answer)
    | (split <;> simp_all only [Std.bind_assoc, bind_ok, Std.uncurry])

end Itasca.Interp

namespace Itasca.Interp
open Aeneas Aeneas.Std WebAssembly Itasca.Platform

/-- The proof recorder's events are matched by callbacks of the real invocation.
Argument validation, allocation and result readback do not call the host. -/
theorem recorded_invoke_observations {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (calls : Observation.Call memory hooks floats allocator)
    (state : runtime.interp.Execution × runtime.store.Store M)
    (platform : P × List (HostObservation M)) (address : runtime.FuncAddr)
    (buffers : Slice runtime.Value × alloc.vec.Vec runtime.Value) (events : List HostEvent)
    (initial : ObservationExtension [] platform.2 events)
    (out : InvocationResult M (P × List (HostObservation M)) × List HostEvent)
    (run : recordedInvokeWith memory (observing hooks) floats allocator state.1 state.2 platform
      address buffers.1 buffers.2 events = .ok out) :
    ObservationExtension [] out.1.2.2.2.1.2 out.2 := by
  obtain ⟨exec,store⟩ := state
  unfold recordedInvokeWith at run
  obtain ⟨metadata,_,run⟩ := Computation.bind_ok_inv _ _ _ run
  cases metadata with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok,Std.uncurry] at run
    have same := Result.ok_injective run
    subst out
    exact initial
  | Ok signature =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok] at run
    obtain ⟨accepted,_,run⟩ := Computation.bind_ok_inv _ _ _ run
    cases accepted with
    | Err error =>
      simp only [
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok,Std.uncurry] at run
      have same := Result.ok_injective run
      subst out
      exact initial
    | Ok unitValue =>
      simp only [bind_ok] at run
      obtain ⟨params,_,run⟩ := Computation.bind_ok_inv _ _ _ run
      cases params with
      | Err error =>
        simp only [
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok,Std.uncurry] at run
        have same := Result.ok_injective run
        subst out
        exact initial
      | Ok params =>
        simp only [bind_ok] at run
        obtain ⟨results,_,run⟩ := Computation.bind_ok_inv _ _ _ run
        cases results with
        | Err error =>
          simp only [
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok,Std.uncurry] at run
          have same := Result.ok_injective run
          subst out
          exact initial
        | Ok results =>
          simp only [lift,bind_ok] at run
          obtain ⟨⟨status,ready⟩,_,run⟩ := Computation.bind_ok_inv _ _ _ run
          simp only [Std.uncurry] at run
          cases status with
          | Err error =>
            simp only [
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok] at run
            have same := Result.ok_injective run
            subst out
            exact initial
          | Ok unitValue =>
            simp only [bind_ok] at run
            obtain ⟨frames,_,run⟩ := Computation.bind_ok_inv _ _ _ run
            obtain ⟨words,_,run⟩ := Computation.bind_ok_inv _ _ _ run
            obtain ⟨⟨⟨status,entered,entryStore,entryPlatform⟩,callTrace⟩,called,run⟩ := Computation.bind_ok_inv _ _ _ run
            unfold recordedCall Recording.run at called
            obtain ⟨callOut,callRun,called⟩ := Computation.bind_ok_inv _ _ _ called
            have same := Result.ok_injective called
            cases same
            have callObserved := initial.append
              (calls _ store platform.1 address 0#usize platform.2 _ callRun)
            simp only [Std.uncurry] at run
            cases status with
            | Err error =>
              simp only [
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok] at run
              have same := Result.ok_injective run
              subst out
              exact callObserved
            | Ok unitValue =>
              simp only [bind_ok] at run
              obtain ⟨⟨⟨id,words,frames,args,defaults,after,next,status⟩,trace⟩,loopRun,run⟩ := Computation.bind_ok_inv _ _ _ run
              have observed := recorded_loop_observations memory hooks floats allocator
                (observing_step_of_call memory hooks floats allocator calls) [] (entered,entryStore,entryPlatform,.Ok ()) _ callObserved _ loopRun
              simp only [Std.uncurry] at run
              cases status with
              | Err error =>
                simp only [
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok] at run
                have same := Result.ok_injective run
                subst out
                exact observed
              | Ok unitValue =>
                simp only [bind_ok] at run
                obtain ⟨metadata,_,run⟩ := Computation.bind_ok_inv _ _ _ run
                cases metadata with
                | Err error =>
                  simp only [
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok] at run
                  have same := Result.ok_injective run
                  subst out
                  exact observed
                | Ok signature =>
                  simp only [bind_ok] at run
                  obtain ⟨⟨status,reserved⟩,_,run⟩ := Computation.bind_ok_inv _ _ _ run
                  simp only [Std.uncurry] at run
                  cases status with
                  | Err error =>
                    simp only [
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,bind_ok,bind_tc_ok] at run
                    have same := Result.ok_injective run
                    subst out
                    exact observed
                  | Ok unitValue =>
                    simp only [bind_ok] at run
                    obtain ⟨empty,_,run⟩ := Computation.bind_ok_inv _ _ _ run
                    obtain ⟨⟨after,returned⟩,_,run⟩ := Computation.bind_ok_inv _ _ _ run
                    simp only [Std.uncurry] at run
                    have same := Result.ok_injective run
                    subst out
                    exact observed
end Itasca.Interp

end

end
