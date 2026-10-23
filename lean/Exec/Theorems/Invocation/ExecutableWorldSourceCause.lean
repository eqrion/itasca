import Exec.Theorems.Invocation.InvokeWorldResources
import Exec.Theorems.Invocation.InvokeHostWorldResources
import Exec.Theorems.Api.ExecutableInv

/-! Source resource causes at the public invocation boundary. Construction is
separate so clients can use the vocabulary without importing the public proof. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Resource and boundary errors retain the original public selection or the
actual reached code world, including functions published by earlier callbacks. -/
def ExecutableWorldInvocationSourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ((error=.BadArguments ∨ error=.WrongStore) ∧ after=store) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    ((∃ ii fi,function.code=.Wasm ii fi ∧
      WorldDefinedSourceResourceCause
        memory hooks floats allocator view code (ExecutableInv view) store Spec.invocationFrame address signature args after error) ∨
     ∃ identity,function.code=.Host identity ∧ InitialHostSourceResourceCause hooks allocator store after identity signature error)

end Exec.Theorems
