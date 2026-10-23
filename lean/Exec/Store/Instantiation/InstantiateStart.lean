import Exec.Store.Instantiation.InstantiateNoStart
import Exec.Store.Initialization.SegmentCodeMetadata

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The exact fresh-execution start invocation remaining in instantiation. -/
def instantiate_start {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (store : runtime.store.Store M) (platform : P) :
    Result (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool) := do
  let execution ← runtime.interp.Execution.new
  let arguments ← lift (Array.to_slice (Std.Array.empty runtime.Value))
  let (result, _, after, host, _) ← runtime.interp.invoke_with memory hooks floats allocator
    execution store platform address arguments (alloc.vec.Vec.new runtime.Value)
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue _ => .ok (.Ok identity, after, host, true)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok (error, after, host, true)

end Exec.Store
