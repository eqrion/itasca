import Exec.Spec.Open.Host
import Exec.Store.Api.ApiMetadata
import Exec.Store.Invariant.CheckedValues
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Host.Chosen.HostChoiceMatching
import Exec.Interp.Host.HostRecording
import Exec.Theorems.Host.HostReturnedActions
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Dynamic checking turns any issued raw reply into an admissible source
reply. Ill-typed values and explicit host errors trap after committed effects. -/
theorem checked_reply_admissible {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (beforeCode afterCode : Store.CodeInterpretation)
    (before after : runtime.store.Store M)
    (effect : ReturnedWorldEffect view (ExecutableInv view) beforeCode before afterCode after)
    (signature : Itasca.types.FuncType) (values : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (issued : ∀value∈values.val,Store.IssuedValue after value) :
    (checkedHostReply memory view afterCode after signature values status).Admissible
      (Store.decodeStore view beforeCode before) (signature.results.val.map sourceType) := by
  classical
  refine ⟨effect.extension,effect.invariant.source_typed,?_⟩
  intro returned selected
  simp only [checkedHostReply] at selected
  split at selected
  · rename_i accepted
    simp only [Option.some.injEq] at selected
    subst returned
    have post := Store.check_values_source_typed memory view afterCode after effect.invariant.well_formed
      values.slice signature.results.slice issued
    rw [accepted.2,WP.spec_ok] at post
    exact (post rfl).1
  · cases selected

/-- An actual completed native resumption logs precisely the dynamically
checked reply and the original copied arguments. This equation assumes only
that this particular resumption returned, not that host control terminates. -/
theorem host_resume_events {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (exec : runtime.interp.Execution) (address : runtime.FuncAddr) (base : Usize)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (hf : store.funcs.val[address.index.val]?=some function) (hs : store.types.val[function.signature.val]?=some signature)
    (values : alloc.vec.Vec runtime.Value) (status : core.result.Result Unit runtime.platform.HostError)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) (token : P)
    (actual : hostResume memory exec store address base values status=.ok out) :
    hostCallEvents address (out.1,out.2,store,token)=
      [.call address.index.val (exec.host_args.val.map sourceValue)
        (checkedHostReply memory view code store signature values status).result] := by
  classical
  cases status with
  | Err error =>
    cases error <;> simp only [hostResume,Result.ok.injEq] at actual
    all_goals subst out
    all_goals simp [hostCallEvents,checkedHostReply]
  | Ok unit =>
    cases unit
    obtain ⟨found,foundEq,same⟩ := WP.spec_imp_exists (vec_index_given store.funcs address.index function hf)
    subst found
    change core.slice.index.Usize.index address.index store.funcs.slice=.ok function at foundEq
    obtain ⟨found,signatureEq,same⟩ := WP.spec_imp_exists (vec_index_given store.types function.signature signature hs)
    subst found
    change core.slice.index.Usize.index function.signature store.types.slice=.ok signature at signatureEq
    obtain ⟨checked,checker,accepted⟩ := WP.spec_imp_exists (check_values_accepts_iff memory store values.slice signature.results.slice)
    simp only [hostResume,alloc.vec.Vec.index,core.slice.index.SliceIndexUsizeSlice,foundEq,signatureEq,checker,bind_ok] at actual
    cases checked with
    | Err error =>
      simp only [runtime.interp.check_failed,bind_ok,ite_true,Result.ok.injEq] at actual
      subst out
      simp [hostCallEvents,checkedHostReply,checker]
    | Ok unit =>
      cases unit
      simp only [runtime.interp.check_failed,bind_ok,Bool.false_eq_true,ite_false] at actual
      obtain ⟨words,encoded,same⟩ := Itasca.ResultFacts.bind_ok_inv _ _ _ actual
      simp only [Result.ok.injEq] at same
      subst out
      simp [hostCallEvents,checkedHostReply,checker]

/-- A captured source host request has the exact result signature retained in
the raw function/type tables; no dynamic result-typing assumption is needed. -/
theorem pending_signature_results {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (pending : Spec.OpenHost.Pending) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (beforeEq : pending.before=Store.decodeStore view code store) (addressEq : pending.address=address.index.val)
    (hf : store.funcs.val[address.index.val]?=some function) (hs : store.types.val[function.signature.val]?=some signature) :
    pending.results=signature.results.val.map sourceType := by
  obtain ⟨sourceModule,sourceAt⟩ := pending.host
  simp only [beforeEq,addressEq,Store.decodeStore,List.getElem?_map,hf,Option.map_some] at sourceAt
  have equal := congrArg funcinst.TYPE (Option.some.inj sourceAt)
  rw [Store.decodeFunction_type code store function (List.getElem?_eq_some_iff.mp hs).1,
    (List.getElem?_eq_some_iff.mp hs).2] at equal
  simp only [Store.decodeFuncType,functype.mk_functype.injEq,list.mk_list.injEq] at equal
  exact equal.2.symm

/-- A completed checked interaction compresses to the original atomic source
host step with its exact final store and dynamically checked outer event.
Its expanded nested history remains an independent retained observation. -/
theorem pending_checked_compress {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (beforeCode afterCode : Store.CodeInterpretation)
    (before after : runtime.store.Store M)
    (effect : ReturnedWorldEffect view (ExecutableInv view) beforeCode before afterCode after)
    (pending : Spec.OpenHost.Pending) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (beforeEq : pending.before=Store.decodeStore view beforeCode before) (addressEq : pending.address=address.index.val)
    (hf : before.funcs.val[address.index.val]?=some function) (hs : before.types.val[function.signature.val]?=some signature)
    (exec : runtime.interp.Execution) (base : Usize) (values : alloc.vec.Vec runtime.Value)
    (status : core.result.Result Unit runtime.platform.HostError)
    (issued : ∀value∈values.val,Store.IssuedValue after value)
    (argsEq : exec.host_args.val.map sourceValue=pending.arguments)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution) (token : P)
    (actual : hostResume memory exec after address base values status=.ok out) :
    StepH pending.initial (hostCallEvents address (out.1,out.2,after,token))
      (pending.completed (checkedHostReply memory view afterCode after signature values status)) := by
  have resultsEq := pending_signature_results view beforeCode before pending address function signature beforeEq addressEq hf hs
  have admissible := checked_reply_admissible memory view beforeCode afterCode before after effect signature values status issued
  have source := pending.compress (checkedHostReply memory view afterCode after signature values status)
    (by simpa only [beforeEq,resultsEq] using admissible)
  have events := host_resume_events memory view afterCode after exec address base function signature
    (effect.metadata.function_lookup hf) (effect.metadata.type_lookup hs) values status out token actual
  rw [events,argsEq,←addressEq]
  exact source
end Exec.Theorems.OpenReentrantControl
