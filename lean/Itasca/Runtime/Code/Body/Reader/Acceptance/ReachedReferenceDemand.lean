import Itasca.Runtime.Code.Local.Capacity.BodyResourceRoom
import Itasca.Runtime.Code.Local.Demand.RecordedDemand
import Itasca.Runtime.Code.Body.Reader.Common.ReaderBasic

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Construct actual callback demand from the independent reference reader and
its remaining source body. The caller supplies source validity evidence and
numeric room, not a target callback result or accepted compiler trace. -/
theorem reference_reader_demand {A R : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A} {length bound position}
    (final : List Observation)
    (room : BodyResourceRoom initial length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate position)
    (metadata : CompilerStable initial compiler) (codeBudget : SourceCodeBudget compiler position)
    (sources : SourceAligned compiler) (cursor : compiler.next_source.val ≤ position)
    (remaining : position < length)
    (read : Result (core.result.Result R error.OpError × code.OpIterState))
    (action : R → Action) (before after : List Observation) (out : code.BodyState)
    (reference : CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out.core,after))
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (tail : code.body_loop_loop recorder data env ctx index profile after out = .ok (.Ok (),final)) :
    CallbackDemand compiler out.core bound := by
  obtain ⟨value,_,called⟩ := reader_run_success _ _ _ _ _ reference
  have vectors := source_callback_demand before after final out.core (action value) (.Ok ()) out data env ctx index profile
    (.Ok ()) called tail
  exact room.demand budget metadata codeBudget sources cursor remaining out.core vectors.1

end Itasca.Runtime.Code
