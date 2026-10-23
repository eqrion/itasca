import Exec.Theorems.Composition.Eventful.EventfulCausalLoop
import Exec.Theorems.Host.HostDispatchCauses
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp

/-- Actual ordinary failures retain their decoded store; actual host failures
retain the selected call and its concrete allocation/interrupt/callback cause. -/
def EventfulDispatchCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (machine : EventfulMachine M P view code expected)
    (out : EventfulDispatchResult M P) (error : runtime.ExecError) : Prop :=
  (CumulativeFailure allocator hooks machine.exec machine.store machine.platform machine.source error ∧
    Store.decodeStore view code out.2.2.1=machine.source.store) ∨
  HostDispatchCause memory hooks floats allocator machine.exec machine.store machine.platform machine.source out error
end Exec.Theorems
