import Itasca.Visitor.ReaderAcceptedProgress
import Exec.Code.Body.Reader.Acceptance.ReaderProfileAcceptanceWasm1
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Exec.Code.Local.Capacity.BodyResourceRoom
import Exec.Code.Local.Capacity.BodyReplay
import Exec.Code.Local.Demand.RecordedDemand

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent single-event Wasm 1 reading supplies all local compiler
resource bounds, including source cursor and closing coordinates. -/
theorem IndexedTableReaderCompilerPointWasm1.capacity_from_source_read {A R : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns localTypes
      data env ctx bodyBt st)
    (before after final : List Observation) (out : code.BodyState) (bound : Nat)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.pos.val)
    (index : U32) (nonempty : st.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.pos.val+1) (inbounds : st.pos.val<data.length) (opcode : U8)
    (read : Result (core.result.Result R error.OpError × code.OpIterState)) (action : R → Action)
    (description : code.step recorder {st with pos := next} data env ctx opcode before =
      CoreVisitor.run read (fun log state value => invoke recorder log (.op state (action value))) before)
    (reference : code.step_profile recorder {core := {st with pos := next}} data env ctx index .Wasm1 opcode before =
      .ok (.Ok (),out,after))
    (byte : data.val[st.pos.val] = opcode)
    (suffix : code.body_loop_loop recorder data env ctx index .Wasm1 before {core := st} = .ok (.Ok (),final)) :
    CallbackCapacity compiler out.core bound 3 ∧ ScopeDemand compiler out.core bound ∧
      compiler.function.body_start.val+out.core.pos.val ≤ Usize.max ∧ next.val ≤ out.core.pos.val := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have raw := profile_raw_success_wasm1 recorder _ out data env ctx index opcode before after reference
  have actualRaw := raw
  rw [← byte] at actualRaw
  have moved := pending.accepted_after recorder before after out.core actualRaw
  have actualReference := reference
  rw [← byte] at actualReference
  have tail := code.body_loop_loop.accepted_tail recorder data env ctx index .Wasm1 ⟨st⟩ out before after final
    nonempty inbounds next advance actualReference suffix
  rw [description] at raw
  obtain ⟨value,_,called⟩ := reader_run_success _ _ _ _ _ raw
  have operands := (source_callback_demand before after final out.core (action value) (.Ok ()) out data env ctx index
    .Wasm1 (.Ok ()) called tail).1
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor (count := 3) (bytes := 1) (by omega) (by decide) out.core operands
  have scope := room.scope budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor state.compiled.controlBudget inbounds out.core operands
  obtain ⟨_,_,_,_,_,_,_,bodyStart,_⟩ := state.compiled.metadata.fields
  refine ⟨capacity,scope,?_,moved.2.1⟩
  rw [bodyStart]
  have coordinate := room.coordinate
  have endBound := moved.2.2
  omega

end Exec.Code
