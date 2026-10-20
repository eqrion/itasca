import Exec.Code.Body.Reader.Simd.SimdPrefixAcceptance
import Exec.Code.Body.Reader.Acceptance.RecordedReaderAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem reader_source_event {R : Type}
    (read : Result (core.result.Result R error.OpError × code.OpIterState)) (action : R → Action)
    (before after : List Observation) (out : code.OpIterState)
    (reference : CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out,after)) :
    ∃ actual, invoke recorder before (.op out actual) = .ok (.Ok (),after) := by
  obtain ⟨value,_,called⟩ := reader_run_success _ _ _ _ _ reference
  exact ⟨action value,called⟩

/-- Every successful SIMD reader ends in its actual recorded source event at
the final reader state. Unsupported subopcodes cannot supply this premise. -/
theorem source_simd_callback (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (before after : List Observation)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    ∃ action, invoke recorder before (.op out.core action) = .ok (.Ok (),after) := by
  obtain ⟨capacity,sub,next,decoded,raw⟩ := simd_prefix_success recorder st out data env ctx index before after reference
  cases pure : Wasm2.Simd.pureMeaning sub.val with
  | some op =>
    rw [Wasm2.Simd.subStep.pure _ _ _ _ _ _ op pure] at raw
    exact reader_source_event _ (fun (_ : Unit) => .simd sub) before after out.core raw
  | none =>
    cases lane : Wasm2.Simd.laneMeaning sub.val with
    | some op =>
      rw [Wasm2.Simd.subStep.lane _ _ _ _ _ _ op lane] at raw
      exact reader_source_event _ (fun lane => .simd_lane sub lane) before after out.core raw
    | none =>
      cases memory : Wasm2.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · rw [Wasm2.Simd.subStep.memory _ _ _ _ _ _ op memory full] at raw
          exact reader_source_event _ (fun arg => .simd_memory sub arg) before after out.core raw
        · rw [Wasm2.Simd.subStep.memoryLane _ _ _ _ _ _ op memory full] at raw
          exact reader_source_event _ (fun arg : code.MemArg × U8 => .simd_memory_lane sub arg.1 arg.2)
            before after out.core raw
      | none =>
        simp only [Wasm2.Simd.subStep,Wasm2.Simd.pure_table,pure,Wasm2.Simd.lane_table,lane,
          Wasm2.Simd.memory_table,memory,Option.map_none,bind_ok] at raw
        split at raw
        · exact reader_source_event _ (fun bits : U64 × U64 => .simd_const bits.1 bits.2) before after out.core raw
        · exact reader_source_event _ (fun bits : U64 × U64 => .simd_shuffle bits.1 bits.2) before after out.core raw
        · simp at raw

end Exec.Code
