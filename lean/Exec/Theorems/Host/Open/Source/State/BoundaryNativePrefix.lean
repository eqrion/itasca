import Exec.Theorems.Host.Open.Driver.QuietBoundaryAtomic
import Exec.Theorems.Host.Open.Driver.AtomicLoopBoundary
import Exec.Theorems.Host.Open.Driver.ActiveWasmTrace
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp Exec.Interp.OpenCall

/-- An independent finite source Wasm segment yields actual active driver
ticks up to the first suspension or inactive Wasm state. Capacity refusal is
an inactive native boundary; matching its outcome uses source resource bounds. -/
theorem source_boundary_native_prefix {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat) {M F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (compatible : GrowthChoicesCompatible memory allocator view choices) (select : Selector)
    {expected : List valtype} (world : EventfulWorld M Unit view expected)
    (held : ExecutableInv view world.code world.machine.store) {count endpoint}
    (prefixSteps : Spec.ChosenStepsN choices occurrence count (Abs.decode world.machine.source) [] endpoint)
    (boundary : Spec.OpenHost.QuietBoundary endpoint)
    (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (stack : List Continuation) (history : List Observation) :
    ∃ticks reached,ActiveWasmTrace memory floats allocator select ticks
      ⟨world.machine.store,.wasm world.machine.exec (.Ok ()) root results,stack,history⟩ reached ∧ NativeWasmBoundary reached := by
  obtain ⟨result,actual,state,invariant,stopped,finished⟩:=WP.spec_imp_exists
    (quiet_boundary_atomic_terminates admissible numericChoice vector occurrence memory floats allocator correct allocation
      view laws compatible world held prefixSteps boundary)
  obtain ⟨ticks,reached,path,stops⟩:=atomic_loop_open_boundary memory floats allocator select
    (ReentrantCallbacks.FloorInv view world.machine.store.externs.length)
    (⟨world,occurrence⟩ : ChosenWorld M Unit view expected)
    state invariant stopped root results stack history
  exact continuing_first_wasm_boundary memory floats allocator select path world.machine.exec root results rfl stops
end Exec.Theorems.OpenReentrantControl
