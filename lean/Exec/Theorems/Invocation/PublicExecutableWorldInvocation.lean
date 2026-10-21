import Exec.Theorems.Invocation.PublicExecutableWorldResources

/-! Ordinary public invocation is a projection of recorded resource correspondence. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
/-- Issued public function handles may denote either Wasm or host functions.
The actual API checks retain exact unchanged-state rejection; accepted calls
preserve the full invariant and refine source results, errors and store effects. -/
theorem invoke_executable_world_issued {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀c store,ExecutableInv view c store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀value∈args.val,Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃ out => ExecutableWorldInvocationOutcome view code store exec platform results initial out ⦄div := by
  apply WP.dspec_mono (invoke_executable_world_source_resources memory hooks floats allocator correct allocation interrupts view laws code
      sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked)
  intro out post
  obtain ⟨events,recorded,outcome,causes⟩ := post
  exact outcome.erase
end Exec.Theorems
