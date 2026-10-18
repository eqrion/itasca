import Exec.Theorems.Invocation.PublicExecutableWorldResources
namespace Exec.Theorems
open Aeneas Aeneas.Std

/-- The public invocation cause rules out object exhaustion. In particular,
this follows from the returned source-resource projection, without replaying
or assuming anything about a callback's internal allocation behavior. -/
theorem ExecutableWorldInvocationSourceCause.no_objects {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store after : runtime.store.Store M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {error : runtime.ExecError}
    (cause : ExecutableWorldInvocationSourceCause memory hooks floats allocator view code store address args after error) :
    error ≠ .Exhausted .Objects := by
  intro same
  subst error
  simp only [ExecutableWorldInvocationSourceCause,WorldDefinedSourceResourceCause,
    CanonicalInvocationResourceCause,WorldLoopResourceCause,EventfulSourceResourceCause,
    InitialHostSourceResourceCause] at cause
  simp at cause

theorem ExecutableInvocationSourceCause.no_objects {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store after : runtime.store.Store M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {error : runtime.ExecError}
    (cause : ExecutableInvocationSourceCause memory hooks floats allocator view code store address args after error) :
    error ≠ .Exhausted .Objects := by
  intro same
  subst error
  simp only [ExecutableInvocationSourceCause,CanonicalInvocationResourceCause,
    ReachedEventfulResourceCause,EventfulSourceResourceCause,InitialHostSourceResourceCause] at cause
  simp at cause
end Exec.Theorems
