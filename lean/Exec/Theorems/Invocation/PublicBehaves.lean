import Exec.Theorems.Invocation.PublicExecutableWorldDivergence

/-! The behavior of a public invocation: every returned result is a recorded source outcome with
classified resource causes, and divergence is an infinite source run. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- A returned result carries the exact event log of `recordedInvokeWith`, the source outcome for
that log and a resource cause for every error. Divergence is an infinite source run. -/
def InvocationBehaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (outcome : Result (core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value)) : Prop :=
  outcome ⦃ out => ∃ events,
    recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out,events) ∧
    ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
    ∀ error, out.1 = .Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view
      (ExecutableInv view) code store address args out.2.2.1 error ⦄div ∧
  (outcome = .div → Spec.InfiniteSourceWithEvents initial)

theorem invoke_executable_world_behaves {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.Laws memory hooks floats allocator view) (code : Store.CodeInterpretation)
    (callbacks : HostLaws hooks view (ExecutableInv view))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (issued : Store.ExternalIssued store (.Func address))
    (argumentIssued : ∀ value ∈ args.val, Store.IssuedValue store value)
    (initial : config)
    (invoked : fun_invoke (Store.decodeStore view code store) address.index.val (args.val.map sourceValue) initial) :
    InvocationBehaves memory hooks floats allocator view code exec store platform address args results initial
      (runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results) :=
  ⟨invoke_executable_world_source_resources memory hooks floats allocator view laws code callbacks exec store
      platform valid address args results issued argumentIssued initial invoked,
    invoke_executable_world_infinite_source memory hooks floats allocator view laws code callbacks exec store
      platform valid address args results issued argumentIssued initial invoked⟩

/-- Without an infinite source run, a behaving invocation returns. -/
theorem InvocationBehaves.returns {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M} {platform : P}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {outcome}
    (behaves : InvocationBehaves memory hooks floats allocator view code exec store platform address args results
      initial outcome)
    (finite : ¬ Spec.InfiniteSourceWithEvents initial) :
    outcome ⦃ out => ∃ events,
      recordedInvokeWith memory hooks floats allocator exec store platform address args results [] = .ok (out,events) ∧
      ExecutableWorldRecordedOutcome memory view code store exec platform address args results initial out events ∧
      ∀ error, out.1 = .Err error → ExecutableWorldInvocationSourceCause memory hooks floats allocator view
        (ExecutableInv view) code store address args out.2.2.1 error ⦄ := by
  obtain ⟨returned,diverged⟩ := behaves
  cases returned with
  | ret post => exact .ret post
  | div => exact (finite (diverged rfl)).elim

end Exec.Theorems
