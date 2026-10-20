import Exec.Theorems.Invocation.InvokeWorldDivergence
import Exec.Theorems.Invocation.InvokeWorld
import Exec.Theorems.Invocation.InvokeHostWorld
import Exec.Theorems.Api.ExecutableInv
import Exec.Interp.Invocation.InvokeCheckedMutable
import Exec.Interp.Relations.ArgumentRejectionKind
import Exec.Store.Invariant.IssuedArguments
import Exec.Spec.Invocation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Public source correspondence with the full API invariant, including hosts.
Event lists are source witnesses; complete recording-log equality is separate. -/
def WorldInvariantInvocationOutcome {M P : Type} (view : M → Slice U8)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  Inv afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1) ∧
  (∃events body,StepsH initial events ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,body⟩) ∧
  (out.1=.Ok () → (∃events,StepsH initial events
    ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
    (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
  (∀error,out.1=.Err error →
    ((error=.BadArguments ∨ error=.WrongStore) ∧ out=(.Err error,exec,before,platform,results)) ∨
    ∃events,EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error)

theorem WorldInvariantInvocationOutcome.of_executed {M P : Type}
    {view : M → Slice U8} {Inv : Store.CodeInterpretation → runtime.store.Store M → Prop} {code afterCode : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out}
    (agrees : Store.CodeAgreesOn before code afterCode)
    (retained : Inv afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1))
    (success : out.1=.Ok () → (∃events,StepsH initial events
      ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
      (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value))
    (failure : ∀error,out.1=.Err error → ∃events,
      EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error) :
    WorldInvariantInvocationOutcome view Inv code before exec platform results initial out := by
  refine ⟨afterCode,agrees,retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : out.1 with
  | Ok value =>
    cases value
    obtain ⟨events,steps⟩ := (success status).1
    exact ⟨events,_,steps⟩
  | Err error =>
    obtain ⟨events,outcome⟩ := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨events,body,steps⟩

/-- Issued public function handles may denote either Wasm or host functions.
The actual API checks retain exact unchanged-state rejection; accepted calls
preserve the full invariant and refine source results, errors and store effects. -/
theorem invoke_world_invariant_issued {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (project : ∀code store,Inv code store → ExecutableInv view code store)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (sound : HostWorldSound hooks view (Inv))
    (preserve : ∀c store,Inv c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,Inv c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,Inv c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => WorldInvariantInvocationOutcome view Inv code store exec platform results initial out ⦄div := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  have early : ∀error,(error=.BadArguments ∨ error=.WrongStore) →
      WorldInvariantInvocationOutcome view Inv code store exec platform results initial (.Err error,exec,store,platform,results) := by
    intro error kind
    refine ⟨code,(by intro index inst found fn; rfl),valid,.refl _,Spec.extend_store_refl _ (project code store valid).well_formed,?_,?_,?_⟩
    · refine ⟨[],vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val],?_⟩
      simpa only [sourceEq] using StepsH.refl initialWf
    · intro impossible; cases impossible
    · intro failed same
      cases same
      exact Or.inl ⟨kind,rfl⟩
  by_cases owner : address.store=store.id
  · have bound : address.index.val<store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val<store.types.val.length :=
      ((project code store valid).shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
    apply WP.dspec_mono (invoke_with_checked_outcome memory hooks floats allocator exec store platform
      address function signature args results owner hf hs
      (WorldInvariantInvocationOutcome view Inv code store exec platform results initial) ?_)
    · intro out post
      rcases post with ⟨error,rejected,rfl⟩ | ⟨checked,done⟩
      · exact early error (check_values_error_kind memory store args (alloc.vec.Vec.deref signature.params) error rejected)
      · exact done
    · intro checked
      have owned := Store.checked_arguments_owned memory view code store (project code store valid).well_formed
        args (alloc.vec.Vec.deref signature.params) argumentIssued checked
      cases kind : function.code with
      | Wasm ii fi =>
        apply WP.dspec_mono (invoke_defined_world_outcomes Abs.executable_language memory hooks floats allocator correct allocation interrupts view laws code
          (Inv) (fun c s held=>(project c s held).toCertifiedApiStore.toCertifiedSupportedStore)
          update sound preserve externs issuedResults exec store platform valid Spec.invocationFrame ambientWf address function signature
          ii fi args results owner owned hf hs kind checked)
        intro out post
        obtain ⟨afterCode,fresh,kept,agrees,extension,success,failure⟩ := post
        apply WorldInvariantInvocationOutcome.of_executed agrees ⟨fresh,kept,extension⟩
        · intro ok
          obtain ⟨typed,sourceOwned,⟨events,steps⟩,rawOwned⟩ := success ok
          exact ⟨⟨events,by simpa only [sourceEq] using steps⟩,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using failure error failed
      | Host identity =>
        have total := invoke_host_world_outcomes memory hooks floats allocator allocation interrupts view code
          (Inv) (fun c s held=>(project c s held).shape) exec store platform valid (project code store valid).well_formed
          Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned checked
          (fun p=>sound code store valid p identity)
          (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
        apply WP.dspec_mono (WP.spec_dspec _ _ _ total)
        intro out post
        obtain ⟨afterCode,⟨fresh,agrees,kept,extension,count⟩,success,failure⟩ := post
        apply WorldInvariantInvocationOutcome.of_executed agrees ⟨fresh,kept,extension⟩
        · intro ok
          obtain ⟨typed,sourceOwned,step,rawOwned⟩ := success ok
          exact ⟨⟨_,by simpa only [sourceEq] using Spec.stepsH_single step⟩,rawOwned⟩
        · intro error failed
          simpa only [sourceEq] using failure error failed
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret (early .WrongStore (Or.inr rfl))

/-- Actual public invocation divergence has a coherent infinite labeled source
execution under the full API invariant and the explicit callback laws. -/
theorem invoke_world_invariant_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (project : ∀code store,Inv code store → ExecutableInv view code store)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (sound : HostWorldSound hooks view (Inv))
    (preserve : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents initial := by
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  by_cases owner : address.store=store.id
  · have bound : address.index.val<store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val<store.types.val.length :=
      ((project code store valid).shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
    have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address function signature args results owner hf hs divergent
    have owned := Store.checked_arguments_owned memory view code store (project code store valid).well_formed
      args (alloc.vec.Vec.deref signature.params) argumentIssued accepted
    cases kind : function.code with
    | Wasm ii fi =>
      have infinite := invoke_defined_world_infinite_source Abs.executable_language memory hooks floats allocator
        correct allocation interrupts view laws code (Inv)
        (fun c s held=>(project c s held).toCertifiedApiStore.toCertifiedSupportedStore)
        update sound preserve externs issuedResults
        exec store platform valid Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs kind divergent
      simpa only [sourceEq] using infinite
    | Host identity =>
      have total := invoke_host_world_outcomes memory hooks floats allocator allocation interrupts view code
        (Inv) (fun c s held=>(project c s held).shape) exec store platform valid (project code store valid).well_formed
        Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned accepted
        (fun p=>sound code store valid p identity)
        (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
      rw [divergent] at total
      exact False.elim (WP.spec_div.mp total)
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner] at divergent
    simp at divergent


theorem invoke_world_invariant_terminates {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (Inv : Store.CodeInterpretation → runtime.store.Store M → Prop)
    (project : ∀code store,Inv code store → ExecutableInv view code store)
    (update : ∀code before after,Inv code before → CumulativeStoreMutation view code before after → Inv code after)
    (sound : HostWorldSound hooks view (Inv))
    (preserve : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,Inv code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : Inv code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => WorldInvariantInvocationOutcome view Inv code store exec platform results initial out ⦄ := by
  have notdiv : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results ≠ .div := by
    intro divergent
    exact finite (invoke_world_invariant_infinite_source memory hooks floats allocator correct allocation interrupts
      view laws code Inv project update sound preserve externs issuedResults exec store platform valid address args results
      issued argumentIssued initial invoked divergent)
  have safe := invoke_world_invariant_issued memory hooks floats allocator correct allocation interrupts view laws code
    Inv project update sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked
  generalize answerEq : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = answer at safe notdiv ⊢
  cases safe with
  | ret post => exact .ret post
  | div => exact False.elim (notdiv rfl)
end Exec.Theorems
