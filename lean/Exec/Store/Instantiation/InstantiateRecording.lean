import Exec.Store.Instantiation.InstantiateStart
import Exec.Interp.Invocation.InvokeRecordingErasure
namespace Exec.Store
open Aeneas Aeneas.Std SpecExt

abbrev InstantiateInnerResult (M P : Type) :=
  core.result.Result runtime.InstanceAddr runtime.ExecError × runtime.store.Store M × P × Bool

/-- Start instrumentation delegates to the actual invocation recorder. -/
def recordedInstantiateStart {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (store : runtime.store.Store M) (platform : P) (prior : List HostEvent) :
    Result (InstantiateInnerResult M P × List HostEvent) := do
  let execution ← runtime.interp.Execution.new
  let arguments ← lift (Array.to_slice (Std.Array.empty runtime.Value))
  let ((result, _, after, host, _),trace) ← Interp.recordedInvokeWith memory hooks floats allocator
    execution store platform address arguments (alloc.vec.Vec.new runtime.Value) prior
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue _ => .ok ((.Ok identity, after, host, true),trace)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok ((error, after, host, true),trace)

/-- Instrumentation at the optional start cutpoint. The accepted-module source
proof establishes the initializer prefix has an empty event trace. -/
def recordedInstantiateTail {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (identity : runtime.InstanceAddr) (store : runtime.store.Store M) (platform : P)
    (prior : List HostEvent) : Result (InstantiateInnerResult M P × List HostEvent) := do
  let (result, store, platform) ← runtime.interp.initialize_segments memory hooks floats allocator store platform identity.index
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let inst ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.store.ModuleInst) store.instances identity.index
    let env ← runtime.compiler.ExecutableModule.env inst.module
    let start ← module.Env.start env
    match start with
    | none => .ok ((.Ok identity, store, platform, true),prior)
    | some function =>
      let index ← lift (UScalar.cast .Usize function)
      let address ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.FuncAddr) inst.funcs index
      recordedInstantiateStart memory hooks floats allocator identity address store platform prior
  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok ((error, store, platform, true),prior)

/-- Preparation is the extracted computation, with logging attached only at
its committed tail. Every rejected preparation returns its unchanged log. -/
def recordedInstantiateInner {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (store : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P) (committed : Bool) (prior : List HostEvent) :
    Result (InstantiateInnerResult M P × List HostEvent) := do
  let (result, staged, platform) ← runtime.store.instantiate.Store.prepare_instance memory hooks floats
    allocator store module imports platform
  let branch ← core.result.Result.Insts.CoreOpsTry.branch result
  match branch with
  | core.ops.control_flow.ControlFlow.Continue (identity, items) =>
    let charged ← staged.instance_items + items
    recordedInstantiateTail memory hooks floats allocator identity
      {staged with instance_items := charged} platform prior
  | core.ops.control_flow.ControlFlow.Break residual =>
    let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      runtime.InstanceAddr (core.convert.FromSame runtime.ExecError) residual
    .ok ((error, staged, platform, committed), prior)
end Exec.Store
