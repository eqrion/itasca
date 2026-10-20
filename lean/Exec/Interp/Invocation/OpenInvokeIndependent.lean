import Exec.Interp.Invocation.OpenInvoke
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std
/-- Public preparation depends on interrupts but never calls a host hook. -/
theorem prepareInvoke_independent {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (left right : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (token : P) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (interrupts : ∀p,left.interrupt p=right.interrupt p) :
    prepareInvoke memory left floats allocator exec store token address args results=
      prepareInvoke memory right floats allocator exec store token address args results := by
  have same : prepareCall memory left floats allocator=prepareCall memory right floats allocator := by
    funext e s p a b
    exact prepareCall_independent memory left right floats allocator e s p a b interrupts
  simp only [prepareInvoke,same]
end Exec.Interp.OpenCall
