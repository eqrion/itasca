import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Progress.UniformDispatchProgress
import Exec.Interp.Machines.Uniform.UniformEventful
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
/-- Actual eventful dispatch plus concrete silent geometry, independent of all
future function publications. -/
structure UniformEventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine M P view code expected) (events : List SpecExt.HostEvent)
    (after : EventfulMachine M P view code expected) : Prop extends
      EventfulTransition memory hooks floats allocator before events after where
  uniform : UniformConcreteSim before.pc after.pc before.pending after.pending before.source after.source events

end Exec.Theorems
