import Exec.Theorems.Composition.Eventful.EventfulHistory
import Exec.Theorems.Progress.UniformDispatchProgress
import Exec.Interp.Machines.Uniform.UniformEventful
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
/-- Actual eventful dispatch plus concrete silent geometry, independent of all
future function publications. -/
structure UniformEventfulTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    (before : EventfulMachine emission allowed M P view code expected) (events : List SpecExt.HostEvent)
    (after : EventfulMachine emission allowed M P view code expected) : Prop extends
      EventfulTransition memory hooks floats allocator before events after where
  uniform : UniformConcreteSim before.pc after.pc before.pending after.pending before.source after.source events

theorem uniform_eventful_history_progress {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation} {expected : List valtype}
    {before after : EventfulMachine emission allowed M P view code expected} {n events}
    (history : Spec.Iterations (UniformEventfulTransition memory hooks floats allocator) n before events after) :
    ∃ count, Spec.StepsHN count (Abs.decode before.source) events (Abs.decode after.source) ∧
      n / (2 * U32.max + 2) ≤ count := by
  exact uniform_dispatch_history_progress (fun s => s.source) (fun s => s.pc) (fun s => s.pending)
    (fun _ => True) (fun _ _ _ _ _ => trivial) (fun s _ => s.invariant.typed.typed.decode_wf)
    (fun _ _ _ _ step => step.uniform) history trivial
end Exec.Theorems
