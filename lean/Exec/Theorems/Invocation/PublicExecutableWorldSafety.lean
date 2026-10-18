import Exec.Theorems.Invocation.PublicExecutableWorldInvocation
import Exec.Spec.InvocationExists
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- All issued public handles and argument values are safe, including foreign
handles whose numeric index is absent from the receiving store. No source
invocation or typing premise is needed; normal results preserve the full store
invariant and extension. Divergence remains permitted. -/
theorem invoke_executable_world_safe {M P F A : Type}
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
    : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results
      ⦃out => ∃afterCode, Store.CodeAgreesOn store code afterCode ∧ ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix store out.2.2.1 ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view afterCode out.2.2.1)⦄div := by
  by_cases owner : address.store=store.id
  · have bound : address.index.val<(Store.decodeStore view code store).FUNCS.length := by
      simpa only [Store.decodeStore,List.length_map] using issued owner
    have values : Forall wf_val (args.val.map sourceValue) := by
      intro value member
      obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
      exact sourceValue_wf raw
    obtain ⟨initial,invoked⟩ := Spec.invocation_exists valid.well_formed address.index.val bound _ values
    apply WP.dspec_mono (invoke_executable_world_issued memory hooks floats allocator correct allocation interrupts
      view laws code sound preserve externs issuedResults exec store platform valid address args results issued argumentIssued initial invoked)
    intro out post
    obtain ⟨afterCode,agrees,fresh,kept,extension,rest⟩ := post
    exact ⟨afterCode,agrees,fresh,kept,extension⟩
  · rw [invoke_wrong_store memory hooks floats allocator exec store platform address args results owner]
    exact WP.dspec.ret ⟨code,(by intro index inst found fn; rfl),valid,.refl _,Spec.extend_store_refl _ valid.well_formed⟩
end Exec.Theorems
