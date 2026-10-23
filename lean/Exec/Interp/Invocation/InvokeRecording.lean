import Exec.Interp.Calls.CallRecording
import Exec.Interp.Invocation.InvokeLoopRecording
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt

abbrev InvocationResult (M P : Type) := core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
  runtime.store.Store M × P × alloc.vec.Vec runtime.Value

/-- Transparent writer instrumentation of the extracted public invocation.
Only the initial call and dispatch loop append events. All argument checks,
preparation errors and result readback follow the original control flow. -/
def recordedInvokeWith {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (func : runtime.FuncAddr) (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (prior : List HostEvent) : Result (InvocationResult M P × List HostEvent) := do
  let r ← runtime.store.Store.func_type memory store func
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let s := alloc.vec.Vec.deref val.params
    let r1 ←
      runtime.interp.check_values memory store args s
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
            runtime.interp.Execution.ensure allocator exec needed
              store.limits.max_values
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let v ← runtime.clear exec1.frames
            let v1 ←
              runtime.interp.invoke_with_loop0 exec1.slots args val.params 0#usize
                0#usize
            let ((r5, exec2, store1, platform1),callTrace) ←
              recordedCall memory hooks
                floats allocator
                { exec1 with store := store.id, slots := v1, frames := v } store platform func 0#usize prior
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let ((i, v5, v6, v7, v8, store2, platform2, status),loopTrace) ←
                recordedInvokeLoop memory
                  hooks floats allocator
                  exec2 store1 platform1 (core.result.Result.Ok ()) callTrace
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch status
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r6 ←
                  runtime.store.Store.func_type memory store2
                    func
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r6
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val3 =>
                  let i1 := alloc.vec.Vec.len val3.results
                  let i2 := alloc.vec.Vec.len results
                  let i3 ← lift (core.num.Usize.saturating_sub i1 i2)
                  let (r7, results1) ←
                    runtime.reserve allocator results i3
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r7
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let results2 ← runtime.clear results1
                    let (store3, results3) ←
                      runtime.interp.invoke_with_loop2 v5 store2 results2
                        0#usize 0#usize val3.results
                    Result.ok ((core.result.Result.Ok (),
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store3, platform2, results3),loopTrace)
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    let r8 ←
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                        Unit (core.convert.FromSame
                        _root_.Exec.runtime.ExecError) residual
                    Result.ok ((r8,
                      {
                        store := i,
                        slots := v5,
                        frames := v6,
                        host_args := v7,
                        host_results := v8
                      }, store2, platform2, results1),loopTrace)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r7 ←
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      Unit (core.convert.FromSame
                      _root_.Exec.runtime.ExecError) residual
                  Result.ok ((r7,
                    {
                      store := i,
                      slots := v5,
                      frames := v6,
                      host_args := v7,
                      host_results := v8
                    }, store2, platform2, results),loopTrace)
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r6 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                    residual
                Result.ok ((r6,
                  {
                    store := i,
                    slots := v5,
                    frames := v6,
                    host_args := v7,
                    host_results := v8
                  }, store2, platform2, results),loopTrace)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r6 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                  residual
              Result.ok ((r6, exec2, store1, platform1, results),callTrace)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r5 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                residual
            Result.ok ((r5, exec1, store, platform, results),prior)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r4 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
              residual
          Result.ok ((r4, exec, store, platform, results),prior)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
        Result.ok ((r3, exec, store, platform, results),prior)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
      Result.ok ((r2, exec, store, platform, results),prior)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
    Result.ok ((r1, exec, store, platform, results),prior)

end Exec.Interp
