import Exec.Generated.Funs

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The remaining generated instantiation computation after the committed item
charge. The cut-point theorem identifies this expression inside the actual
monolithic function before making any claims about start-function execution. -/
def instantiate_tail {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P) :
    Result (core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool) := do
  let (result, store, platform) ← runtime.interp.initialize_segments memory hooks floats allocator store platform identity.index
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let inst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.store.ModuleInst) store.instances identity.index
    let env ← runtime.compiler.ExecutableModule.env inst.module
    let start ← module.Env.start env
    match start with
    | none => .ok (.Ok identity, store, platform, true)
    | some function =>
      let index ← lift (UScalar.cast .Usize function)
      let address ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.FuncAddr) inst.funcs index
      let execution ← runtime.interp.Execution.new
      let arguments ← lift (Array.to_slice (Std.Array.empty runtime.Value))
      let (result, _, store, platform, _) ← runtime.interp.invoke_with memory hooks floats allocator
        execution store platform address arguments (alloc.vec.Vec.new runtime.Value)
      let branch ← core.result.Result.Insts.CoreOpsTry.branch result
      match branch with
      | core.ops.control_flow.ControlFlow.Continue _ => .ok (.Ok identity, store, platform, true)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
        .ok (error, store, platform, true)

  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok (error, store, platform, true)

end Exec.Store
