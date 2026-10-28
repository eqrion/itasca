import Exec.Interp.Host.HostResume
import Exec.Interp.Host.HostPreparationCauses

/-! Resumable extracted-call adapter. Preparation executes the actual native
checks and scratch-buffer operations, then exposes a pending host call before
any callback is run. Its continuation uses the existing dynamic host resume. -/
noncomputable section
namespace Exec.Interp.OpenCall
open Aeneas Aeneas.Std Result
abbrev Answer (M P : Type) := core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P
inductive CallPhase (M P : Type) where
  | done (answer : Answer M P)
  | pending (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
      (address : runtime.FuncAddr) (base : Usize) (identity : U64)
      (args defaults : alloc.vec.Vec runtime.Value)

def prepareCall
  {M : Type} {P : Type} {F : Type} {A : Type} (platformMemoryBufferInst :
  runtime.platform.MemoryBuffer M) (platformPlatformInst :
  runtime.platform.Platform P M) (platformFloatOpsInst :
  runtime.platform.FloatOps F) (platformAllocInst : runtime.platform.Alloc A)
  (exec : _root_.Exec.runtime.interp.Execution)
  (store : _root_.Exec.runtime.store.Store M) (platform : P)
  (func : _root_.Exec.runtime.FuncAddr) (base : Std.Usize) :
  Result (CallPhase M P)
  := do
  let (r, platform1) ←
    runtime.interp.interrupt platformMemoryBufferInst platformPlatformInst
      platform
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let f ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        _root_.Exec.runtime.store.FuncInst) store.funcs func.index
    match f.code with
    | runtime.store.FuncCode.Host id =>
      let ty ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          _root_.Itasca.types.FuncType) store.types f.signature
      let s := alloc.vec.Vec.deref ty.results
      let r1 ← runtime.interp.type_slots s
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let s1 := alloc.vec.Vec.deref ty.params
        let r2 ← runtime.interp.type_slots s1
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let size ← lift (core.cmp.impls.OrdUsize.max val val1)
          let o ← lift (Usize.checked_add base size)
          match o with
          | none =>
            ok (.done (core.result.Result.Err (runtime.ExecError.Exhausted
              runtime.ResourceLimit.Values), exec, store, platform1))
          | some n =>
            let (r3, exec1) ←
              runtime.interp.Execution.ensure platformAllocInst exec n
                store.limits.max_values
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let i := alloc.vec.Vec.len ty.params
              let i1 := alloc.vec.Vec.len exec1.host_args
              let args_add ← lift (core.num.Usize.saturating_sub i i1)
              let (r4, v) ←
                runtime.reserve platformAllocInst exec1.host_args args_add
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let i2 := alloc.vec.Vec.len ty.results
                let i3 := alloc.vec.Vec.len exec1.host_results
                let results_add ← lift (core.num.Usize.saturating_sub i2 i3)
                let (r5, v1) ←
                  runtime.reserve platformAllocInst exec1.host_results
                    results_add
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let v2 ← runtime.clear v
                  let v3 ← runtime.clear v1
                  let v4 ←
                    runtime.interp.call_loop0 exec1.slots v2 store.id
                      ty.params 0#usize base
                  let v5 ← runtime.interp.call_loop1 v3 ty.results 0#usize
                  let s2 := alloc.vec.Vec.deref v4
                  let (s3, deref_mut_back) ←
                    lift (alloc.vec.Vec.deref_mut v5)
                  ok (.pending {exec1 with host_args := v4} store platform1 func base id v4 v5)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  let r6 ←
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                      Unit (core.convert.FromSame
                      _root_.Exec.runtime.ExecError) residual
                  ok (.done (r6, { exec1 with host_args := v, host_results := v1 },
                    store, platform1))
              | core.ops.control_flow.ControlFlow.Break residual =>
                let r5 ←
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                    Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                    residual
                ok (.done (r5, { exec1 with host_args := v }, store, platform1))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r4 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                  residual
              ok (.done (r4, exec1, store, platform1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ←
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
              Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
              residual
          ok (.done (r3, exec, store, platform1))
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
        ok (.done (r2, exec, store, platform1))
    | runtime.store.FuncCode.Wasm «instance» function =>
      let i := alloc.vec.Vec.len exec.frames
      if i >= store.limits.max_frames
      then
        ok (.done (core.result.Result.Err (runtime.ExecError.Exhausted
          runtime.ResourceLimit.CallStack), exec, store, platform1))
      else
        let i1 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Exec.runtime.store.ModuleInst) store.instances «instance»
        let code1 ←
          alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
            _root_.Exec.runtime.bytecode.CompiledFunction) i1.module.functions
            function
        let i2 ← lift (UScalar.cast .Usize code1.slot_count)
        let o ← lift (Usize.checked_add base i2)
        match o with
        | none =>
          ok (.done (core.result.Result.Err (runtime.ExecError.Exhausted
            runtime.ResourceLimit.Values), exec, store, platform1))
        | some n =>
          let (r1, exec1) ←
            runtime.interp.Execution.ensure platformAllocInst exec n
              store.limits.max_values
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let i3 ← lift (UScalar.cast .Usize code1.param_slots)
            let i4 ← base + i3
            let exec2 ←
              runtime.interp.call_loop3 exec1 base code1.local_slots i4
            let (r2, v) ←
              runtime.reserve platformAllocInst exec2.frames 1#usize
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let v1 ←
                alloc.vec.Vec.push v
                  ({ «instance», function, pc := 0#u32, base } :
                  _root_.Exec.runtime.interp.Frame)
              ok (.done (core.result.Result.Ok (), { exec2 with frames := v1 }, store,
                platform1))
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r3 ←
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                  Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                  residual
              ok (.done (r3, { exec2 with frames := v }, store, platform1))
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r2 ←
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
                Unit (core.convert.FromSame _root_.Exec.runtime.ExecError)
                residual
            ok (.done (r2, exec1, store, platform1))
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Exec.runtime.ExecError) residual
    ok (.done (r1, exec, store, platform1))

end Exec.Interp.OpenCall
