import Exec.Store.Instantiation.InstantiateStart

/-! The actual instantiation start wrapper and its fresh invocation buffers. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std

def startExecution : runtime.interp.Execution :=
  { store := 0#usize, slots := alloc.vec.Vec.new _, frames := alloc.vec.Vec.new _,
    host_args := alloc.vec.Vec.new _, host_results := alloc.vec.Vec.new _ }

def startArguments : Slice runtime.Value := Array.to_slice (Std.Array.empty runtime.Value)

theorem start_equation {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (store : runtime.store.Store M) (platform : P) :
    Store.instantiate_start memory hooks floats allocator identity address store platform = (do
      let (status, _, after, host, _) ← runtime.interp.invoke_with memory hooks floats allocator
        startExecution store platform address startArguments (alloc.vec.Vec.new runtime.Value)
      match status with
      | .Ok _ => .ok (.Ok identity, after, host, true)
      | .Err error => .ok (.Err error, after, host, true)) := by
  simp only [Store.instantiate_start, runtime.interp.Execution.new, lift, bind_ok]
  apply congrArg (fun next => Std.bind (runtime.interp.invoke_with memory hooks floats allocator
    startExecution store platform address startArguments (alloc.vec.Vec.new runtime.Value)) next)
  funext ⟨status, execution, after, host, results⟩
  cases status <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

end Exec.Theorems
