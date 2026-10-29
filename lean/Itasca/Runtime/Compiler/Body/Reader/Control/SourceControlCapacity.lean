import Itasca.Runtime.Compiler.Body.Reader.Control.ControlKind
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPoint
import Itasca.Runtime.Compiler.Local.Demand.RecordedDemand
import Itasca.Runtime.Compiler.Local.Capacity.BodyResourceRoom
import Itasca.Runtime.Compiler.Local.Capacity.BodyReplay

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent control-reader success and its retained source suffix supply
all instruction, control, operand, reserve, slot, and end-coordinate demands.
No compiler callback success or caller-supplied capacity record is needed. -/
theorem IndexedTableReaderCompilerPointWasm2.control_capacity_from_source {A : Type}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (before after final : List Observation) (out : code.BodyState) (bound : Nat)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (kind : ControlReaderKind) (byte : data.val[st.core.pos.val] = kind.opcode)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    CallbackCapacity compiler out.core bound 3 ∧ ScopeDemand compiler out.core bound ∧
      compiler.function.body_start.val+out.core.pos.val ≤ Usize.max ∧ st.core.pos.val < out.core.pos.val := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨observations,_,trace⟩ := kind.records pending recorder id recorder_records ⟨sourceLocals,ft.results⟩
    byte before (.Ok ()) out after canonical
  obtain ⟨token,chunk⟩ := trace.accepted
  have endBound := chunk.encoded.span
  change st.core.pos.val < out.core.pos.val ∧ out.core.pos.val ≤ data.length at endBound
  rw [kind.dispatch] at canonical
  obtain ⟨value,_,called⟩ := reader_body_success _ _ _ _ _ _ canonical
  have operands := (source_callback_demand before after final out.core (kind.action value) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) called tail).1
  have capacity := room.capacity budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor (bytes := 1) (count := 3) (by omega) (by decide) out.core operands
  have scope := room.scope budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor state.compiled.controlBudget inbounds out.core operands
  obtain ⟨_,_,_,_,_,_,_,bodyStart,_⟩ := state.compiled.metadata.fields
  refine ⟨capacity,scope,?_,endBound.1⟩
  rw [bodyStart]
  have coordinate := room.coordinate
  omega

end Itasca.Runtime.Compiler
