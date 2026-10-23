import Exec.Theorems.Host.Open.Source.State.TickDone
import Exec.Theorems.Host.Open.Driver.DriverPrefixes
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std SpecExt Exec.Interp

theorem guarded_done_store {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (native : State M)
    (guard : StateGuard memory view code native) (shape : native.Shape .invocation)
    (outcome : Outcome M) (actual : tick memory floats allocator select native=.ok (.done outcome)) :
    outcome.store=native.store := by
  have boundary:=tick_done_boundary memory floats allocator select native .invocation shape outcome actual
  rcases native with ⟨store,mode,stack,history⟩
  cases mode <;> cases stack <;> simp [Erased.Nonterminal,Erased.state] at boundary
  · cases shape
  · simp only [tick,Result.ok.injEq,ControlFlow.done.injEq] at actual
    subst outcome
    exact guard.2.1.1

end Exec.Theorems.OpenReentrantControl
