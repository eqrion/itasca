import Itasca.Runtime.Interp.Invocation.InvokeRecording
import Itasca.Runtime.Platform.RecordingBind
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
/-- Erasing the writer recovers the extracted invocation for arbitrary hooks
and internal states, including failure and divergence. -/
theorem recordedInvokeWith_erase {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) :
    (do let (out,_) ← recordedInvokeWith memory hooks floats allocator exec store platform func args results prior
        Result.ok out) = runtime.interp.invoke_with memory hooks floats allocator exec store platform func args results := by
  unfold recordedInvokeWith runtime.interp.invoke_with
  simp only [recordedCall,Platform.Recording.run,Std.uncurry,Std.bind_assoc,bind_ok]
  repeat' first
    | rfl
    | (apply Platform.Recording.bind_erase_cont _ _ _ _ (recordedInvokeLoop_erase ..)
       intro answer trace
       rcases answer with ⟨id,words,frames,hostArgs,hostResults,after,host,status⟩
       simp only [Std.bind_assoc,bind_ok,Std.uncurry])
    | (apply congrArg (Std.bind _)
       funext answer)
    | (split <;> simp only [Std.bind_assoc,bind_ok,Std.uncurry])

end Itasca.Runtime.Interp
