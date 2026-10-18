import Exec.Theorems.Invocation.InvokeExecutableRecorded
import Exec.Theorems.Invocation.InvokeHostRecorded
import Exec.Interp.Invocation.InvokeRecordedChecks
import Exec.Interp.Invocation.InvokeRecordingErasure
import Exec.Interp.Relations.ArgumentRejectionKind
import Exec.Store.Invariant.IssuedArguments
import Exec.Spec.Invocation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Public source correspondence at the exact concrete invocation log, including
initial hosts, body callbacks and unchanged empty-log API rejections. -/
def ExecutableRecordedInvocationOutcome {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) (events : List HostEvent) : Prop :=
  ExecutableInv view code out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view code out.2.2.1) ∧
  (∃body,StepsH initial events ⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,body⟩) ∧
  (out.1=.Ok () → (StepsH initial events
    ⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
    (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
  (∀error,out.1=.Err error →
    ((error=.BadArguments ∨ error=.WrongStore) ∧ out=(.Err error,exec,before,platform,results) ∧ events=[]) ∨
    EventfulInvocationError initial events (Store.decodeStore view code out.2.2.1) Spec.invocationFrame error)

theorem ExecutableRecordedInvocationOutcome.of_executed {M P : Type}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out} {events : List HostEvent}
    (retained : ExecutableInv view code out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view code out.2.2.1))
    (success : out.1=.Ok () → (StepsH initial events
      ⟨⟨Store.decodeStore view code out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
      (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value))
    (failure : ∀error,out.1=.Err error →
      EventfulInvocationError initial events (Store.decodeStore view code out.2.2.1) Spec.invocationFrame error) :
    ExecutableRecordedInvocationOutcome view code before exec platform results initial out events := by
  refine ⟨retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : out.1 with
  | Ok value =>
    cases value
    exact ⟨_,(success status).1⟩
  | Err error =>
    have outcome := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨body,steps⟩

/-- Issued public function handles may denote either Wasm or host functions.
The actual API checks retain exact unchanged-state rejection; accepted calls
preserve the full invariant and refine source results, errors and store effects. -/
theorem invoke_executable_recorded_issued {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    recordedInvokeWith memory hooks floats allocator exec store platform address args results []
      ⦃ (out,events) => ExecutableRecordedInvocationOutcome view code store exec platform results initial out events ⦄div := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,(error=.BadArguments ∨ error=.WrongStore) →
      ExecutableRecordedInvocationOutcome view code store exec platform results initial (.Err error,exec,store,platform,results) [] := by
    intro error kind
    refine ⟨valid,.refl _,Spec.extend_store_refl _ valid.well_formed,?_,?_,?_⟩
    · refine ⟨vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val],?_⟩
      simpa only [sourceEq] using StepsH.refl initialWf
    · intro impossible; cases impossible
    · intro failed same
      cases same
      exact Or.inl ⟨kind,rfl,rfl⟩
  by_cases owner : address.store=store.id
  · have bound : address.index.val<store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val<store.types.val.length :=
      (valid.shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
    apply WP.dspec_mono (recorded_invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results [] owner hf hs
      (fun (out,events)=>ExecutableRecordedInvocationOutcome view code store exec platform results initial out events) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store valid.well_formed
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_executable_recorded memory hooks floats allocator correct allocation interrupts view laws code
          sound preserve externs issuedResults exec store platform valid Spec.invocationFrame ambientWf address function signature
          ii fi args results owner owned hf hs kind checked)
        rintro ⟨out,events⟩ post
        apply ExecutableRecordedInvocationOutcome.of_executed post.1
        · intro success
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := post.2.1 success
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using post.2.2 error failed
      | Host identity =>
        have total := invoke_host_recorded_outcomes memory hooks floats allocator allocation interrupts view code
          (ExecutableInv view code) (fun _ held=>held.shape) sound exec store platform valid valid.well_formed
          Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned checked
          (fun p=>preserve store valid identity p) (fun p=>externs store valid identity p) (fun p=>issuedResults store valid identity p)
        apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
        rintro ⟨out,events⟩ post
        apply ExecutableRecordedInvocationOutcome.of_executed ⟨post.1.1,post.1.2.1,post.1.2.2.1⟩
        · intro success
          obtain ⟨typed,sourceOwned,steps,rawOwned⟩ := post.2.1 success
          exact ⟨by simpa only [sourceEq] using steps,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using post.2.2 error failed
  · rw [recorded_invoke_wrong_store memory hooks floats allocator exec store platform address args results [] owner]
    exact WP.dspec.ret (early .WrongStore (Or.inr rfl))
/-- The extracted public API returns the same result as its concrete recorder,
whose exact log labels the corresponding source execution. -/
theorem invoke_executable_recording_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ∃events,
        recordedInvokeWith memory hooks floats allocator exec store platform address args results []=.ok (out,events) ∧
        ExecutableRecordedInvocationOutcome view code store exec platform results initial out events ⦄div :=
  Platform.Recording.erase_dspec _ _ _
    (recordedInvokeWith_erase memory hooks floats allocator exec store platform address args results [])
    (invoke_executable_recorded_issued memory hooks floats allocator correct allocation interrupts view laws code
      sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked)
end Exec.Theorems
