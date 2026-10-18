import Exec.Code.Body.Relations.Calls.OrdinaryCallbackReady
import Exec.Code.Local.Callbacks.Common.FixupBudget
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

structure ControlCallbackReady {A} (compiler : runtime.compiler.FunctionCompiler A)
    (position : Nat) : Prop where
  pc : compiler.function.code.val.length + 3 < 2^32
  code : compiler.function.code.val.length + 3 ≤ Usize.max
  sources : compiler.function.source_offsets.val.length + 3 ≤ Usize.max
  maps : compiler.function.controls.val.length < Usize.max
  frames : compiler.frames.val.length < Usize.max
  nonempty : 0 < compiler.frames.val.length
  coordinate : compiler.function.body_start.val + position ≤ Usize.max
  emittedCoordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max

theorem StructuredCompilerPrefixWithTables.control_ready {A}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals parents current values position}
    (point : StructuredCompilerPrefixWithTables jumpTables emit initial compiler types functions returns locals parents current values position)
    (length next : Nat) (bounded : length ≤ limits.MAX_MODULE_BYTES.val)
    (positionBound : position ≤ length) (nextBound : next ≤ length)
    (bodyBound : initial.function.body_start.val + length ≤ Usize.max) :
    ControlCallbackReady compiler next := by
  have room := point.codeBudget.callback_headroom (positionBound.trans bounded) point.sources
  have capacities := point.capacities (positionBound.trans bounded)
  have body := point.metadata.body_bound bodyBound
  have cursor := point.cursor
  obtain ⟨prior,frame,frames,_⟩ := point.frames.split
  exact ⟨room.1,room.2.1,room.2.2,capacities.2.2.1,capacities.2.2.2,
    by simp [frames],by omega,by omega⟩

theorem StructuredReaderCompilerStateWithTablesWasm1.frames_length {A}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial compiler types functions returns locals
      data env ctx bodyBt st parents current savedParents savedCurrent) :
    compiler.frames.val.length = st.ctrls.val.length := by
  have physical := List.Forall₂.length_eq state.compiled.frames.frames
  have source := List.Forall₂.length_eq state.sources.parents
  obtain ⟨C,outer,spine,header,base,typed,controls,values⟩ := state.boundary.opened
  have count := congrArg List.length controls
  simp only [List.length_append,List.length_map,List.length_singleton] at physical count
  omega

theorem StructuredReaderCompilerStateWithTablesWasm2.frames_length {A}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {jumpTables emit types functions returns locals data env sourceLocals index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial compiler types functions returns locals
      data env sourceLocals index ft st parents current savedParents savedCurrent) :
    compiler.frames.val.length = st.core.ctrls.val.length := by
  have physical := List.Forall₂.length_eq state.compiled.frames.frames
  have source := List.Forall₂.length_eq state.sources.parents
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := state.boundary.opened
  have count := congrArg List.length controls
  simp only [List.length_append,List.length_map,List.length_singleton] at physical count
  omega

theorem IndexedTableReaderCompilerPointWasm1.control_ready {A}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st}
    (point : IndexedTableReaderCompilerPointWasm1 emit initial compiler types functions returns locals data env ctx bodyBt st)
    (next : Usize) (advance : next.val = st.pos.val+1) (inbounds : st.pos.val < data.length)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    ControlCallbackReady compiler next.val ∧ compiler.frames.val.length = st.ctrls.val.length := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  exact ⟨state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound,state.frames_length⟩

theorem IndexedTableReaderCompilerPointWasm2.control_ready {A}
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial compiler types functions returns locals data env sourceLocals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val < data.length)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    ControlCallbackReady compiler next.val ∧ compiler.frames.val.length = st.core.ctrls.val.length := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  exact ⟨state.compiled.control_ready data.length next.val state.boundary.source_bound
    (by omega) (by omega) bodyBound,state.frames_length⟩

end Exec.Code
