import Exec.Theorems.Host.Callbacks.HostControl
import Exec.Theorems.Invocation.PublicExecutableWorldDivergence

/-! Public invocation instantiated with an executable callback implementation.
Its callback laws are conclusions of the program proofs, not embedder premises. -/
namespace Exec.Theorems.OpenHostControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem ranked_callback_package {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Code)
    (ranking : ∀ identity args, ∃ rank, Ranked (select identity args) rank)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (token : Unit)
    (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (identity : U64) (args results : Slice runtime.Value) :
    (platform memory select).call_host token store identity args results ⦃ answer =>
      ExecutableInv view code answer.2.2.1 ∧ FrameStorePrefix store answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.2.1) ∧
      answer.2.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value ⦄ := by
  obtain ⟨rank,ranked⟩ := ranking identity args
  obtain ⟨answer,actual,_⟩ := WP.spec_imp_exists
    (run_terminates memory (select identity args) rank ranked ⟨0,store,identity,args⟩)
  have safe := run_safe memory (select identity args) view code ⟨0,store,identity,args⟩ held
  rw [actual,WP.dspec_ok] at safe
  simp only [platform,actual,bind_ok]
  exact WP.spec.ret ⟨safe.2.1.invariant,safe.2.1.metadata,safe.2.1.extension,safe.2.1.externs,safe.2.2⟩

theorem ranked_world_sound {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (select : U64 → Slice runtime.Value → Code)
    (ranking : ∀ identity args, ∃ rank, Ranked (select identity args) rank)
    (view : M → Slice U8) : HostWorldSound (platform memory select) view (ExecutableInv view) :=
  HostWorldSound.of_fixed (ranked_sound memory select ranking view)

/-- Absence of source divergence yields an ordinary invocation result with
retained certificates and the actual event trace for ranked checked callbacks.
Allocation, memory, and floating-point laws remain explicit platform boundaries. -/
theorem invoke_ranked_host_terminates {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (select : U64 → Slice runtime.Value → Code)
    (ranking : ∀ identity args, ∃ rank, Ranked (select identity args) rank)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial) :
    runtime.interp.invoke_with memory (platform memory select) floats allocator exec store () address args results
      ⦃ out => ∃ events,
        recordedInvokeWith memory (platform memory select) floats allocator exec store () address args results [] = .ok (out,events) ∧
        ExecutableWorldRecordedOutcome view code store exec () results initial out events ⦄ := by
  have preservation : ∀ code store, ExecutableInv view code store → ∀ host token args results answer,
      (platform memory select).call_host token store host args results = .ok answer →
      FrameStorePrefix store answer.2.2.1 := by
    intro code store held host token args results answer actual
    have post := ranked_callback_package memory select ranking view code token store held host args results
    rw [actual,WP.spec_ok] at post
    exact post.2.1
  have externs : ∀ code store, ExecutableInv view code store → ∀ host token args results answer,
      (platform memory select).call_host token store host args results = .ok answer →
      store.externs.length ≤ answer.2.2.1.externs.length := by
    intro code store held host token args results answer actual
    have post := ranked_callback_package memory select ranking view code token store held host args results
    rw [actual,WP.spec_ok] at post
    rw [post.2.2.2.1]
  have issuedResults : ∀ code store, ExecutableInv view code store → ∀ host token args results answer,
      (platform memory select).call_host token store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value := by
    intro code store held host token args results answer actual
    have post := ranked_callback_package memory select ranking view code token store held host args results
    rw [actual,WP.spec_ok] at post
    exact post.2.2.2.2
  exact invoke_executable_world_terminates memory (platform memory select) floats allocator correct allocation
    (fun _ => WP.spec.ret trivial) view laws code (ranked_world_sound memory select ranking view)
    preservation externs issuedResults exec store () valid address args results issued argumentIssued initial invoked finite

end Exec.Theorems.OpenHostControl
