import Exec.Theorems.Composition.Eventful.EventfulWorldStep
import Exec.Theorems.Progress.UniformDispatchProgress
import Exec.Interp.Machines.Uniform.UniformEventful
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
/-- Actual eventful dispatch plus concrete silent geometry, independent of all
future function publications. -/
structure UniformWorldTransition {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    {view : M → Slice U8} {expected : List valtype}
    (before : EventfulWorld M P view expected) (events : List SpecExt.HostEvent)
    (after : EventfulWorld M P view expected) : Prop extends
      EventfulWorldTransition memory hooks floats allocator before events after where
  uniform : UniformConcreteSim before.machine.pc after.machine.pc before.machine.pending after.machine.pending before.machine.source after.machine.source events

theorem uniform_world_history_progress {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {expected : List valtype}
    {before after : EventfulWorld M P view expected} {n events}
    (history : Spec.Iterations (UniformWorldTransition memory hooks floats allocator) n before events after) :
    ∃ count, Spec.StepsHN count (Abs.decode before.machine.source) events (Abs.decode after.machine.source) ∧
      n / (2 * U32.max + 2) ≤ count := by
  exact uniform_dispatch_history_progress (fun s => s.machine.source) (fun s => s.machine.pc) (fun s => s.machine.pending)
    (fun _ => True) (fun _ _ _ _ _ => trivial) (fun s _ => s.machine.invariant.typed.typed.decode_wf)
    (fun _ _ _ _ step => step.uniform) history trivial
end Exec.Theorems
