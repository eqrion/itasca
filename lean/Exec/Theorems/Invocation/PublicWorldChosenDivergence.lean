import Exec.Theorems.Invocation.InvokeHostWorld
import Exec.Theorems.Invocation.PublicExecutableWorldInvocation
import Exec.Theorems.Invocation.PublicExecutableWorldResources
import Exec.Theorems.Invocation.InvokeWorldDivergence
import Exec.Theorems.Invocation.InvokeWorldChosenDivergence

/-! Divergence reflection for a specified compatible choice policy.
Its compatibility obligations are stronger than existential source choices. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Actual public invocation divergence has a coherent infinite labeled source
execution under the full API invariant and the explicit callback laws. -/
theorem invoke_executable_world_infinite_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (sound : HostWorldChosenSound memory hooks view (ExecutableInv view) choices)
    (preserve : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀code store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results=.div) :
    Spec.InfiniteChosenSource choices 0 initial := by
  have ambientWf := Spec.invocation_frame_wf invoked
  have sourceEq := Spec.invocation_config invoked
  by_cases owner : address.store=store.id
  · have bound : address.index.val<store.funcs.val.length := issued owner
    let function := store.funcs.val[address.index.val]
    have hf : store.funcs.val[address.index.val]?=some function := List.getElem?_eq_getElem bound
    have signatureBound : function.signature.val<store.types.val.length :=
      (valid.shape.functions function (List.mem_of_getElem? hf)).1
    let signature := store.types.val[function.signature.val]
    have hs : store.types.val[function.signature.val]?=some signature := List.getElem?_eq_getElem signatureBound
    have accepted := invoke_divergent_arguments memory hooks floats allocator exec store platform address function signature args results owner hf hs divergent
    have owned := Store.checked_arguments_owned memory view code store valid.well_formed
      args (alloc.vec.Vec.deref signature.params) argumentIssued accepted
    cases kind : function.code with
    | Wasm ii fi =>
      have infinite := invoke_defined_world_infinite_chosen admissible numericChoice vector 0 Abs.executable_language memory hooks floats allocator
        correct allocation interrupts view laws code compatible (ExecutableInv view)
        (fun _ _ held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
        (fun _ _ _ held mutation=>held.update mutation) (fun _ _ held=>held.source_typed) sound preserve externs issuedResults
        exec store platform valid Spec.invocationFrame ambientWf address function signature ii fi args results owner owned hf hs kind divergent
      simpa only [sourceEq] using infinite
    | Host identity =>
      have total := invoke_host_world_outcomes memory hooks floats allocator allocation interrupts view code
        (ExecutableInv view) (fun _ _ held=>held.shape) exec store platform valid valid.well_formed
        Spec.invocationFrame ambientWf address function identity signature args results owner hf kind hs owned accepted
        (fun p=>sound.erases code store valid p identity)
        (fun p=>preserve code store valid identity p) (fun p=>externs code store valid identity p) (fun p=>issuedResults code store valid identity p)
      rw [divergent] at total
      exact False.elim (WP.spec_div.mp total)
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner] at divergent
    simp at divergent

end Exec.Theorems
