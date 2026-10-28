import Itasca.Runtime.Code.Module.InitializerEmitElementsAvailable
import Itasca.Runtime.Code.Module.InitializerEmitDatasAvailable
import Itasca.Runtime.Code.Local.Relations.Common.SegmentAcceptance
import Itasca.Runtime.Code.Local.Relations.Common.SegmentFinish

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The exact extracted suffix after read-only initializer mappings. This is a
proof-only factorization of `initialize.lower`, retaining its actual error,
allocator, and publication branches. It adds no runtime API or external model. -/
def segmentCompilation {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.ExecutableModule ×
      runtime.compiler.Budget A) := do
  let function ←
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new
      _root_.Itasca.runtime.bytecode.Instr) 0#u32
  let (budget4, result3, function1) ←
    runtime.compiler.initialize.lower_loop3 ops module
      budget 0#usize (core.result.Result.Ok ()) function
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch result3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (budget5, result4, function2) ←
      runtime.compiler.initialize.lower_loop4 ops module
        budget4 0#usize result3 function1
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch result4
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r, budget6, v) ←
        runtime.compiler.initialize.emit ops budget5
          function2.code (runtime.bytecode.Instr.Return 0#u32 0#u32)
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let b ←
          runtime.bytecode.CompiledFunction.well_formed
            { function2 with code := v }
        if b
        then
          let i := alloc.vec.Vec.len module.functions
          let (r1, budget7, v1) ←
            runtime.compiler.Budget.push ops budget6
              module.functions { function2 with code := v }
          .ok (r1, { module with functions := v1, initialization := i },
            budget7)
        else
          .ok (core.result.Result.Err
            _root_.Itasca.error.VisitError.OutOfMemory, module, budget6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        .ok (r1, module, budget6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      .ok (r, module, budget5)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    .ok (r, module, budget4)

end Itasca.Runtime.Code
