import Exec.Code.Body.Reader.Table.StructuredReaderPrefixTableWasm1
import Exec.Code.Body.Reader.Table.ReaderTableInputsWasm2
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_table_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    {jumpTables emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable=true → p.current.ctrl.polymorphic_base=false)
    (boundary : CompilerTableBoundary before)
    (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data st.core.pos depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[p.start.val]'p.inbounds=0x0e#u8)
    (accepted : code.branch_table_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env before=.ok (.Ok (),out,after)) :
    ReaderPostWasm2 p out.core (BrTable.instruction depths fallback) true [] ∧
    StructuredCompilerPrefixWithTables jumpTables emit initial after types functions returns locals parents
      (current.advance (BrTable.instruction depths fallback)) out.core.vals.val out.core.pos.val ∧
    CompilerTableBoundary after ∧ after.reachable=false := by
  have post := reader_table_post_wasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    p before after out depths fallback endPos byte encoded accepted
  have sourceAt : Wasm2.At data p.start (.plain (BrTable.instruction depths fallback)) endPos :=
    .plain (.of_table_decoded depths fallback p.inbounds byte p.pos encoded)
  have endEq := (post.encoded.unique sourceAt).2
  have consumed := table_immediate_byte_bound encoded
  have position := p.pos
  obtain ⟨_,_,_,afterBoundary,dead,_⟩ := compiler_reader_table_effect_wasm2 ops law before after st out
    data env p.opened.shape.core depths fallback endPos encoded boundary accepted
  refine ⟨post,?_,afterBoundary,dead⟩
  by_cases live : before.reachable=true
  · obtain ⟨entered,_⟩ := invariant.live live
    obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm2
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      entered (invariant.known live) (monomorphic live) before after out depths fallback endPos encoded accepted
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    have staged := invariant.table_scratch budget buffer
    exact staged.br_table ops law out.core depths fallback blockTypes stack stackEq inputs
      (by simpa only [boundary.depths,List.nil_append] using bufferEq) boundary.targets futureTables tableEq
      (gate stack) (by rw [endEq]; omega) live callback
  · have beforeDead := Bool.eq_false_iff.mpr live
    obtain ⟨budget,buffer,blockTypes,bufferEq,callback⟩ := compiler_table_source_wasm2 ops law before after st out data env
      p.opened.shape.core depths fallback endPos encoded accepted
    obtain ⟨fixed,codeEq,_,frames,_,_,sources,cursor⟩ := compiler_br_table_dead_effect ops law
      {before with budget,table_depths := buffer} after out.core fallback blockTypes beforeDead callback
    have ordinary : CompilerOrdinaryStable before after := by
      refine ⟨?_,fixed.stable.capacity⟩
      change (compilerMetadata after,after.frames,after.function.controls)=
        (compilerMetadata before,before.frames,before.function.controls)
      rw [fixed.stable.metadata,frames,fixed.controls]
      rfl
    exact invariant.skip (BrTable.instruction depths fallback) beforeDead dead ordinary codeEq sources
      (by rw [endEq]; omega) (by rw [cursor])
end Exec.Code
