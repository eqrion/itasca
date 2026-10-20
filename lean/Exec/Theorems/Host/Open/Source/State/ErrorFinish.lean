import Exec.Theorems.Host.Open.Source.State.StateGuard
import Exec.Interp.Host.OpenStoppedLoop
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Error readback returns the exact saved API result without an allocation,
store effect or callback. -/
theorem readback_error_result {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (address : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value) (error : runtime.ExecError) :
    readback memory allocator address results (finishExecution (exec,store,(),.Err error))=
      .ok (.Err error,exec,store,(),results) := by
  cases exec
  simp [readback,finishExecution,bind_tc_eq,bind_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,core.convert.FromSame.from]

/-- A pending native error readback is a source stutter with strict rank drop.
The following invocation-return tick will emit the visible exit observation. -/
theorem source_error_finish {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (select : Selector) (code : Store.CodeInterpretation)
    (native : State M) (source : Spec.OpenExecution.State SourceControl)
    (guard : SourceStateGuard memory allocator view code native source 1)
    (exec : runtime.interp.Execution) (error : runtime.ExecError) (root : runtime.FuncAddr)
    (results : alloc.vec.Vec runtime.Value) (mode : native.mode=.wasm exec (.Err error) root results)
    (sourceMode : source.mode=.invokeReturn (sourceInvocationResult (.Err error) results)) :
    let answer : InvokeAnswer M Unit:=(.Err error,exec,native.store,(),results)
    let next : State M:={native with mode:=.invokeReturn answer}
    tick memory floats allocator select native=.ok (.cont next) ∧
      SourceStateGuard memory allocator view code next source 0 ∧ next.history=native.history := by
  dsimp only
  have stopped : ¬ActiveExecution (exec,native.store,(),.Err error) := by
    rintro ⟨active,good⟩
    cases good
  have prepared := prepareLoop_stopped memory (inert memory) floats allocator (exec,native.store,(),.Err error) stopped
  refine ⟨?_,?_,rfl⟩
  · simp only [tick,mode,prepared,bind_ok,readback_error_result]
  · refine ⟨guard.invariant,?_,guard.stack,guard.storeEq⟩
    rw [sourceMode]
    exact .returned _ rfl (by intro successful; cases successful)
end Exec.Theorems.OpenReentrantControl
