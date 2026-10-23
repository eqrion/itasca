import Exec.Theorems.Host.Open.Native.NativeCallPartial
import Exec.Interp.Invocation.OpenNativeInvocation
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- An inactive native loop exits immediately without calling any host hook. -/
theorem native_execution_stopped {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform Unit M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (status : Status)
    (stopped : ¬(0<exec.frames.length ∧ status=.Ok ())) :
    executionBody memory hooks floats allocator (exec,store,(),status)=
      .ok (.done (finishExecution (exec,store,(),status))) := by
  cases status with
  | Ok unit=>
    cases unit
    have noFrames : ¬exec.frames.len>0#usize := by scalar_tac
    simp [executionBody,runtime.interp.invoke_with_loop1.body,noFrames,finishExecution]
  | Err error=>simp [executionBody,runtime.interp.invoke_with_loop1.body,core.result.Result.is_ok,finishExecution]

def NativeBodyResult {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : ExecutionState M Unit) (root : runtime.FuncAddr) (signature : Itasca.types.FuncType) :
    ControlFlow (ExecutionState M Unit) (ExecutionResult M Unit) → Prop
  | .cont next=>∃afterCode,ReentrantCallbacks.Effect view code before.2.1 afterCode next.2.1 ∧
      WasmTask view afterCode next.2.1 next.1 next.2.2.2 root signature
  | .done finished=>finished=finishExecution before ∧ ¬ActiveExecution before

/-- Native execution is partially safe for the actual combined callback
implementation. Callback divergence may block a native iteration; every
returned iteration retains a full checked effect and typed task certificate. -/
theorem native_body_partial {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (select : Selector)
    (code : Store.CodeInterpretation) (state : ExecutionState M Unit)
    (root : runtime.FuncAddr) (signature : Itasca.types.FuncType)
    (held : ExecutableInv view code state.2.1) (task : WasmTask view code state.2.1 state.1 state.2.2.2 root signature) :
    executionBody memory (platform memory floats allocator select) floats allocator state
      ⦃flow=>NativeBodyResult view code state root signature flow⦄div := by
  rcases state with ⟨exec,store,token,status⟩
  cases token
  by_cases active : 0<exec.frames.length ∧ status=.Ok ()
  · obtain ⟨positive,rfl⟩ := active
    have positiveRaw : exec.frames.len>0#usize := by scalar_tac
    obtain ⟨phase,prepared,ready⟩ := WP.spec_imp_exists (task.prepare memory floats allocator correct allocation view laws held positive)
    rw [←erase_loop_body,prepareLoop_independent memory (platform memory floats allocator select) (inert memory) floats allocator _ (fun _=>rfl)]
    simp only [prepareLoop,if_pos positiveRaw,core.result.Result.is_ok,bind_ok,ite_true,prepared,resumeLoop]
    have safe:=ready.resume_partial memory floats allocator correct allocation view laws select held
    generalize actual : resume memory (platform memory floats allocator select) phase=result at safe ⊢
    cases safe with
    | div=>simp only [actual,bind_div];exact WP.dspec.div _
    | ret post=>
      rename_i answer
      rcases answer with ⟨status,finished,after,token⟩
      cases token
      simp only [actual,Std.uncurry,bind_ok]
      exact WP.dspec.ret post
  · rw [native_execution_stopped memory (platform memory floats allocator select) floats allocator exec store status active]
    exact WP.dspec.ret ⟨rfl,active⟩
end Exec.Theorems.OpenReentrantControl
