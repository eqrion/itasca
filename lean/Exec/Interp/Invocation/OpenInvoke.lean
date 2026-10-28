import Exec.Interp.Host.OpenStep
import Exec.Interp.Invocation.InvokeRecordingErasure
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std Result
abbrev InvokeAnswer (M P : Type) := core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P × alloc.vec.Vec runtime.Value
def readback {M P A : Type} (platformMemoryBufferInst : runtime.platform.MemoryBuffer M)
    (platformAllocInst : runtime.platform.Alloc A) (func : runtime.FuncAddr)
    (results : alloc.vec.Vec runtime.Value)
    (finished : Usize × alloc.vec.Vec U64 × alloc.vec.Vec runtime.interp.Frame × alloc.vec.Vec runtime.Value ×
      alloc.vec.Vec runtime.Value × runtime.store.Store M × P × core.result.Result Unit runtime.ExecError) :
    Result (InvokeAnswer M P) := do
  let (i,v5,v6,v7,v8,store2,platform2,status) := finished
  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch status
  match cf6 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let r6 ←
      runtime.store.Store.func_type platformMemoryBufferInst store2
        func
    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
    match cf7 with
    | core.ops.control_flow.ControlFlow.Continue val3 =>
      let i1 := alloc.vec.Vec.len val3.results
      let i2 := alloc.vec.Vec.len results
      let i3 ← lift (core.num.Usize.saturating_sub i1 i2)
      let (r7, results1) ←
        runtime.reserve platformAllocInst results i3
      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
      match cf8 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let results2 ← runtime.clear results1
        let (store3, results3) ←
          runtime.interp.invoke_with_loop2 v5 store2 results2
            0#usize 0#usize val3.results
        ok (core.result.Result.Ok (),
          {
            store := i,
            slots := v5,
            frames := v6,
            host_args := v7,
            host_results := v8
          }, store3, platform2, results3)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r8 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame
            _root_.Exec.runtime.ExecError) residual
        ok (r8,
          {
            store := i,
            slots := v5,
            frames := v6,
            host_args := v7,
            host_results := v8
          }, store2, platform2, results1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r7 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame
          _root_.Exec.runtime.ExecError) residual
      ok (r7,
        {
          store := i,
          slots := v5,
          frames := v6,
          host_args := v7,
          host_results := v8
        }, store2, platform2, results)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r6 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
        residual
    ok (r6,
      {
        store := i,
        slots := v5,
        frames := v6,
        host_args := v7,
        host_results := v8
      }, store2, platform2, results)

inductive InvokePhase (M P : Type) where
  | done (answer : InvokeAnswer M P)
  | waiting (phase : CallPhase M P) (address : runtime.FuncAddr) (results : alloc.vec.Vec runtime.Value)

def prepareInvoke
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (exec : _root_.Exec.runtime.interp.Execution)
  (store : _root_.Exec.runtime.store.Store M) (platform : P)
  (func : _root_.Exec.runtime.FuncAddr)
  (args : Slice _root_.Exec.runtime.Value)
  (results : alloc.vec.Vec _root_.Exec.runtime.Value) :
  Result (InvokePhase M P)
  := do
  let r ← runtime.store.Store.func_type platformMemoryBufferInst store func
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val.params
    let r1 ←
      runtime.interp.check_values platformMemoryBufferInst store args s
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let s1 := alloc.vec.Vec.deref val.params
      let r2 ← runtime.interp.type_slots s1
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let s2 := alloc.vec.Vec.deref val.results
        let r3 ← runtime.interp.type_slots s2
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let needed ← lift (core.cmp.impls.OrdUsize.max val1 val2)
          let (r4, exec1) ←
            runtime.interp.Execution.ensure platformAllocInst exec needed
              store.limits.max_values
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let v ← runtime.clear exec1.frames
            let v1 ←
              runtime.interp.invoke_with_loop0 exec1.slots args val.params 0#usize
                0#usize
            let phase ← prepareCall platformMemoryBufferInst platformPlatformInst
                platformFloatOpsInst platformAllocInst
                { exec1 with store := store.id, slots := v1, frames := v } store platform func 0#usize
            ok (.waiting phase func results)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                residual
            ok (.done (r5, exec1, store, platform, results))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
              residual
          ok (.done (r4, exec, store, platform, results))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
        ok (.done (r3, exec, store, platform, results))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
      ok (.done (r2, exec, store, platform, results))
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
    ok (.done (r1, exec, store, platform, results))

end Exec.Interp.OpenCall
