import Exec.Theorems.Host.Open.Driver.CallTask
import Exec.Interp.Host.OpenStoppedLoop
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

def PreparedLoopTask {M : Type} (memory : runtime.platform.MemoryBuffer M) (view : M → Slice U8)
    (code : Store.CodeInterpretation) (state : ExecutionState M Unit)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) : LoopPhase M Unit → Prop
  | .finished out=>out=finishExecution state ∧ ¬ActiveExecution state
  | .executing phase=>CallTask memory view code state.2.1 root signature phase

/-- Every certified native loop state prepares normally, even when the
synchronous callback selected by a later resumption can diverge. -/
theorem WasmTask.prepare_loop {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    {code : Store.CodeInterpretation} {state : ExecutionState M Unit}
    {root : runtime.FuncAddr} {signature : Itasca.types.FuncType}
    (held : ExecutableInv view code state.2.1) (task : WasmTask view code state.2.1 state.1 state.2.2.2 root signature) :
    prepareLoop memory (inert memory) floats allocator state ⦃phase=>PreparedLoopTask memory view code state root signature phase⦄ := by
  rcases state with ⟨exec,store,token,status⟩
  cases token
  by_cases active : 0<exec.frames.length ∧ status=.Ok ()
  · obtain ⟨positive,rfl⟩ := active
    have raw : exec.frames.len>0#usize := by scalar_tac
    obtain ⟨phase,actual,ready⟩ := WP.spec_imp_exists (task.prepare memory floats allocator correct allocation view laws held positive)
    simp only [prepareLoop,if_pos raw,core.result.Result.is_ok,bind_ok,ite_true,actual]
    exact WP.spec.ret ready
  · rw [prepareLoop_stopped memory (inert memory) floats allocator (exec,store,(),status) active]
    exact WP.spec.ret ⟨rfl,active⟩
end Exec.Theorems.OpenReentrantControl
