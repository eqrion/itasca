import Exec.Theorems.Invocation.InvokeHostWorld
import Exec.Theorems.Api.ExecutableCallEntry
import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Theorems.Invocation.InvokeWorldDivergence

/-! Public evolving-world divergence reflection and normal-return recovery.
Lookup evidence is shared with terminal correspondence; source productivity remains separate. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Actual public invocation divergence has a coherent infinite labeled source execution, or the
source reaches a store on which a callback diverges, under the full API invariant and the explicit
callback laws. -/
theorem invoke_executable_world_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteSourceWithEvents initial ∨ HostCallDiverged hooks view initial := by
  have initialWf : wf_config initial := by cases invoked; assumption
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  by_cases owner : address.store=store.id
  · obtain ⟨function,signature,hf,hs,signatureBound⟩ := valid.call_entry address issued owner
    have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address function signature args results owner hf hs divergent
    have owned := Store.checked_arguments_owned memory view code store valid.well_formed
      args (alloc.vec.Vec.deref signature.params) argumentIssued accepted
    cases kind : function.code with
    | Wasm ii fi =>
      have infinite := invoke_defined_world_infinite_source memory hooks floats allocator
        view laws code (ExecutableInv view)
        (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
        (fun _ _ _ held mutation=>held.update mutation) callbacks
        exec store platform valid Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs kind divergent
      simpa only [sourceEq] using infinite
    | Host identity =>
      have total := invoke_host_world_outcomes memory hooks floats allocator laws.allocCorrect laws.interruptsReturn view code
        (ExecutableInv view) (fun _ _ held=>held.shape) exec store platform valid valid.well_formed
        Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned accepted
        (fun p=>callbacks.sound code store valid p identity)
        (callbacks.retains code store valid identity)
      have diverged := total.diverged divergent
      subst sourceEq
      exact Or.inr ⟨[],code,store,_,_,StepsH.refl initialWf,diverged⟩
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner] at divergent
    simp at divergent
end Exec.Theorems
