import Exec.Theorems.Invocation.InvokeExecutableEventfulCauses
import Exec.Theorems.Invocation.InvokeHostEventfulCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Public checks or the exact selected Wasm/host invocation explain a failure.
Both causal branches retain source bounds and actual callback decisions. -/
def ExecutableEventfulInvocationCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ((error=.BadArguments ∨ error=.WrongStore) ∧ after=store) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    ((∃ ii fi,function.code=.Wasm ii fi ∧
      DefinedEventfulInvocationCause (emission:=Executable.emission) (allowed:=Abs.ExecutableInstr)
        memory hooks floats allocator view code (ExecutableInv view code) exec store Spec.invocationFrame
        address signature ii fi args results after error) ∨
     ∃ identity,function.code=.Host identity ∧
      InitialHostInvocationCause memory hooks floats allocator view code exec store Spec.invocationFrame
        address identity signature args results after error)
end Exec.Theorems
