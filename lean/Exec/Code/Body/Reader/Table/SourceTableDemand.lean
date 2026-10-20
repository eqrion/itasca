import Exec.Code.Local.Demand.RecordedDemand
import Itasca.Wasm2.Trace.TableBytes

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem table_suffix_final_observation {data start remaining observations result state}
    (trace : Wasm2.CallbackTrace.TableSuffix data start remaining observations result state) :
    result = .Ok () → ∃ prior action reply,
      observations = prior ++ [⟨.op state action,reply⟩] := by
  induction trace with
  | failed error labels count outcomes => intro impossible; cases impossible
  | complete labels length fallback outcomes =>
    intro _
    exact ⟨_,_,_,rfl⟩

/-- The independently accepted table loop records its final marked state.
A retained source body suffix therefore bounds that state by the independent
whole-body demand, without an accepted compiler callback premise. -/
theorem source_table_loop_demand
    (before after final : List Observation) (st : code.OpIterState) (out : code.BodyState)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (profile : ValidationProfile)
    (shape : Control.Shape st) (count : U32)
    (reference : code.branch_table_with_loop recorder st data env before count none 0#u32 =
      .ok (.Ok (),out,after))
    (tail : code.body_loop_loop recorder data env ctx index profile after out = .ok (.Ok (),final)) :
    out.core.vals.length ≤ (observationDemand final).operands ∧
    out.core.ctrls.length ≤ (observationDemand final).controls := by
  obtain ⟨observations,recorded,trace⟩ := Wasm2.CallbackTrace.table_loop_records recorder id recorder_records
    ⟨st⟩ data env shape (by simp) count 0#u32 none (by simp) before (.Ok ()) out after reference
  obtain ⟨suffix,retained⟩ := source_body_recorded_prefix after final out data env ctx index profile (.Ok ()) tail
  obtain ⟨prior,action,reply,events⟩ := table_suffix_final_observation trace rfl
  apply observationDemand.recorded_op (prior := before ++ prior) (suffix := suffix) (action := action) (reply := reply)
  dsimp only [id] at recorded
  simp only [retained,recorded,events,List.append_assoc,List.singleton_append]

end Exec.Code
