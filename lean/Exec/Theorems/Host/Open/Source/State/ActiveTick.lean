import Exec.Theorems.Host.Open.Driver.ReentrantControl
namespace Exec.Theorems.OpenReentrantControl
open Aeneas Aeneas.Std Exec.Interp Exec.Interp.OpenCall

/-- Active native dispatch exposes precisely the prepared call phase. The
executable tick performs no real callback while accepting that phase. -/
theorem wasm_active_tick {M F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A) (select : Selector)
    (state : State M) (exec : runtime.interp.Execution) (root : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)
    (mode : state.mode=.wasm exec (.Ok ()) root results) (active : 0<exec.frames.length)
    (phase : CallPhase M Unit)
    (prepared : prepareStep memory (inert memory) floats allocator exec state.store ()=.ok phase) :
    tick memory floats allocator select state=.ok (.cont (acceptCall select state phase root results)) := by
  have frames : exec.frames.len>0#usize:=by scalar_tac
  have ready : prepareLoop memory (inert memory) floats allocator (exec,state.store,(),.Ok ())=.ok (.executing phase) := by
    simp only [prepareLoop,frames,ite_true,core.result.Result.is_ok,bind_ok,prepared]
  simp only [tick,mode,ready,bind_ok]
end Exec.Theorems.OpenReentrantControl
