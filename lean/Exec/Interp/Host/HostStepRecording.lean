import Exec.Interp.Host.HostRecording
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

/-- At a selected indirect host source site, a retained forward jump does not
call the host. Only the fetched indirect-call bytecode records the checked call. -/
def indirectHostStepEvents {M P : Type} (compiled : runtime.bytecode.CompiledFunction)
    (pc : U32) (address : runtime.FuncAddr)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : List HostEvent :=
  match compiled.code.val[pc.val]? with
  | some (.CallIndirect _ _ _) => hostCallEvents address out
  | _ => []

def recordedIndirectHostStep {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (compiled : runtime.bytecode.CompiledFunction) (pc : U32) (address : runtime.FuncAddr) (prior : List HostEvent) :=
  Platform.Recording.run (runtime.interp.step memory hooks floats allocator exec store platform)
    (indirectHostStepEvents compiled pc address) prior

theorem recordedIndirectHostStep_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (compiled : runtime.bytecode.CompiledFunction) (pc : U32) (address : runtime.FuncAddr) (prior : List HostEvent) :
    (do let (out,_) ← recordedIndirectHostStep memory hooks floats allocator exec store platform compiled pc address prior
        Result.ok out) = runtime.interp.step memory hooks floats allocator exec store platform :=
  Platform.Recording.erase _ _ _
end Exec.Interp
