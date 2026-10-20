import Exec.Code.Body.Reader.Table.TableInstructionRoom
import Exec.Code.Local.Callbacks.Table.CompilerTableBoundary
import Exec.Code.Body.Reader.Table.SourceTableScratchInstructionPrefix
import Exec.Code.Body.Reader.Table.SourceTableScratchExitSlots
import Exec.Code.Body.Reader.Table.ReaderTableDispatchWasm1
import Exec.Code.Body.Reader.Table.ReaderTableWasm1

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Actual Wasm 1 label collection and the complete table callback preserve
instruction checks and recorded exit-slot bounds from independently typed labels. -/
theorem reader_table_open_instructions_wasm1 {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (final : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (boundary : CompilerTableBoundary before)
    (fixups : FixupBudget before.frames.val before.function.code.val.length)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before = .ok (.Ok (),final,after)) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  obtain ⟨fallback,view,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st final data env ctx before after accepted
  obtain ⟨count,first,last,defaultEnd,depths,budget,buffer,countDecoded,labelsDecoded,defaultDecoded,countEq,sameCompiler,bufferEq⟩ :=
    compiler_read_br_table_wasm1 ops law before collected st final data fallback view read
  have encoded : BrTable.Decoded data st.pos depths fallback defaultEnd :=
    ⟨count,first,last,countDecoded,countEq,labelsDecoded,defaultDecoded⟩
  have bufferSource : buffer.val = depths := by simpa only [boundary.depths,List.nil_append] using bufferEq
  have labels : before.reachable = true → ∃ stack,
      Sequence.stackTypes st.vals.val = stack++[.I32] ∧
      ∀ depth ∈ buffer.val++[fallback], ∃ scope discarded,
        (current :: parents.reverse)[depth.val]? = some scope ∧ stack = scope.front++discarded++scope.branchTypes := by
    intro live
    obtain ⟨stack,input,scopes⟩ := reader_table_inputs_wasm1
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      (invariant.live live).1 (invariant.known live) (monomorphic live) before collected final fallback view depths fallback
      defaultEnd encoded read
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
  subst collected
  exact ⟨invariant.br_table_scratch_open_instructions ops law budget buffer final fallback (Control.resultView view)
      fixups room boundary.targets coordinate labels held callback,
    invariant.br_table_scratch_exit_slots ops law budget buffer final fallback (Control.resultView view) labels exits callback⟩

end Exec.Code
