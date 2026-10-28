import Exec.Code.Body.Reader.Acceptance.ReachedStatefulBaseAcceptance
import Exec.Code.Body.Reader.Acceptance.ReachedStatefulBulkAcceptance
import Exec.Code.Body.Reader.Table.IndexedTableReaderCompilerPoint
import Exec.Code.Body.Relations.Common.ReachedCompilerLedger
import Exec.Code.Local.Capacity.BodyResourceRoom
import Exec.Code.Local.Capacity.BodyReplay
import Exec.Code.Local.Demand.RecordedDemand

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual stateful base reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.stateful_base_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (C : context) (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (opcode : U8) (member : opcode.val ∈ [37,38,63,64,208,209,210])
    (byte : data.val[st.core.pos.val] = opcode)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨op,a,b,_,callback,_⟩ := reader_stateful_base_wasm2 pending recorder before after out
    ⟨sourceLocals,ft.results⟩ opcode member byte canonical
  rw [stateful_callback_invoke] at callback
  have operands := (source_callback_demand before after final out.core (statefulAction op a b) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_stateful_base_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ opcode member demand C matched state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.indirect byte canonical

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual stateful bulk reader acceptance. -/
theorem IndexedTableReaderCompilerPointWasm2.stateful_bulk_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (C : context) (matched : EnvTranslation.Matches env ⟨sourceLocals,ft.results⟩ C)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (subopcode : U32) (prefixEnd : Usize) (member : subopcode.val ∈ [8,9,10,11,12,13,14,15,16,17])
    (decoded : Leb128.Decoded data next subopcode prefixEnd)
    (byte : data.val[st.core.pos.val] = 252#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index .Wasm2 data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index .Wasm2
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index .Wasm2 st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨op,a,b,_,callback,_⟩ := reader_stateful_bulk_wasm2 pending recorder before after out
    ⟨sourceLocals,ft.results⟩ subopcode prefixEnd member byte decoded canonical
  rw [stateful_callback_invoke] at callback
  have operands := (source_callback_demand before after final out.core (statefulAction op a b) (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index .Wasm2 (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_profile_stateful_bulk_available_wasm2 pending ops bound allocation recorder before after compiler out
    ⟨sourceLocals,ft.results⟩ subopcode prefixEnd member decoded demand C matched state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.indirect byte canonical

end Itasca.Runtime.Code
