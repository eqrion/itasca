import Exec.Code.Body.Reader.Table.TableInstructionRoom
import Exec.Code.Local.Callbacks.Table.CompilerTableBoundary
import Exec.Code.Body.Reader.Table.SourceTableScratchInstructionPrefix
import Exec.Code.Body.Reader.Table.SourceTableScratchExitSlots
import Exec.Code.Body.Reader.Table.ReaderTableInputsWasm2

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual Wasm 2 label collection and the complete table callback preserve
instruction checks and recorded exit-slot bounds from independently typed labels. -/
theorem reader_table_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (final : code.BodyState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (boundary : CompilerTableBoundary before)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env .Wasm2 before = .ok (.Ok (),final,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨count,first,selector,popped,depths,fallback,view,last,readState,budget,buffer,
      countDecoded,popCall,bufferEq,labelsDecoded,defaultDecoded,countEq,marked,callback⟩ :=
    compiler_read_br_table ops law before after st final data env _ accepted
  have popFacts := code.pop_with_type.total {st.core with pos := first} .I32
    (show Control.Shape {st.core with pos := first} from ⟨p.opened.shape.core.ordered,p.opened.shape.core.bounded⟩)
  rw [popCall,WP.spec_ok] at popFacts
  have popPosition : popped.pos = first := popFacts.2.2.1
  rw [popPosition] at labelsDecoded
  have encoded : BrTable.Decoded data st.core.pos depths fallback readState.core.pos :=
    ⟨count,first,last,countDecoded,countEq,labelsDecoded,defaultDecoded⟩
  have bufferSource : buffer.val = depths := by simpa only [boundary.depths,List.nil_append] using bufferEq
  have labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes st.core.vals.val = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧ stack = scope.front++discarded++scope.branchTypes := by
    intro live
    obtain ⟨stack,input,scopes⟩ := reader_table_inputs_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      (invariant.live live).1 (invariant.known live) (monomorphic live) before after final depths fallback
      readState.core.pos encoded accepted
    refine ⟨stack,input,?_⟩
    intro depth member
    rw [bufferSource] at member
    obtain ⟨scope,discarded,selected,_,stackEq⟩ := scopes depth member
    refine ⟨scope,discarded,?_,stackEq⟩
    simpa only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] using selected
  have coordinate : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
    have cursor := invariant.cursor
    have position := p.inbounds
    omega
  have room : before.function.code.val.length+1+2*(buffer.val.length+1) ≤ Usize.max := by
    rw [bufferSource]
    exact table_instruction_room invariant.codeBudget (by have position := p.pos; omega) encoded sourceBound
  exact ⟨invariant.br_table_scratch_open_instructions ops law budget buffer final.core fallback view
      fixups room boundary.targets coordinate labels held callback,
    invariant.br_table_scratch_exit_slots ops law budget buffer final.core fallback view labels exits callback⟩

end Itasca.Runtime.Code
