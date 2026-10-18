import Exec.Code.Body.Control.Table.StructuredTableScratch
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixTable
import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables
import Exec.Code.Body.Reader.Table.ReaderTableInputsWasm1
import Exec.Code.Body.Reader.Table.ReaderTablePost
import Exec.Code.Body.Reader.Table.ReaderTableEffects
import Exec.Code.Local.Relations.Table.BranchTableDead
import Exec.Code.Local.Capacity.BranchTableSourceGrowth
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_table_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {jumpTables emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : before.reachable=true → p.current.ctrl.polymorphic_base=false)
    (boundary : CompilerTableBoundary before)
    (depths : List U32) (fallback : U32) (endPos : Usize)
    (encoded : BrTable.Decoded data st.pos depths fallback endPos)
    (futureTables : List U32) (tableEq : jumpTables=after.function.jump_tables.val++futureTables)
    (gate : ∀ stack selector start len, emit (stack++[.I32]) (BrTable.instruction depths fallback)
      [.JumpTable selector start len] stack)
    (byte : data.val[p.start.val]'p.inbounds=code.OP_BR_TABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR_TABLE before=.ok (.Ok (),out,after)) :
    ReaderPostWasm1 p out (BrTable.instruction depths fallback) true [] ∧
    StructuredCompilerPrefixWithTables jumpTables emit initial after types functions returns locals parents
      (current.advance (BrTable.instruction depths fallback)) out.vals.val out.pos.val ∧
    CompilerTableBoundary after ∧ after.reachable=false := by
  obtain ⟨actual,common,collected,read,callback⟩ := reader_table_dispatch_wasm1
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx before after accepted
  have post := reader_table_post_wasm1 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    p before collected out actual common depths fallback endPos byte encoded read
  have sourceAt : Wasm1.At data p.start (.plain (BrTable.instruction depths fallback)) endPos :=
    .of_table_decoded depths fallback p.inbounds (by simpa only [global_simps] using byte) p.pos encoded
  have endEq := (post.encoded.unique sourceAt).2
  have consumed := table_immediate_byte_bound encoded
  have position := p.pos
  obtain ⟨_,_,_,afterBoundary,dead,_⟩ := compiler_reader_table_effect_wasm1 ops law before after st out
    data env ctx depths fallback endPos encoded boundary accepted
  refine ⟨post,?_,afterBoundary,dead⟩
  by_cases live : before.reachable=true
  · obtain ⟨entered,_⟩ := invariant.live live
    obtain ⟨stack,stackEq,inputs⟩ := reader_table_inputs_wasm1
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) p same fronts invariant.entryChain
      entered (invariant.known live) (monomorphic live) before collected out actual common depths fallback endPos encoded read
    obtain ⟨rfl,budget,buffer,collectedEq,bufferEq⟩ := compiler_table_source_wasm1 ops law before collected st out data
      actual common depths fallback endPos encoded read
    subst collected
    have staged := invariant.table_scratch budget buffer
    exact staged.br_table ops law out depths actual (Control.resultView common) stack stackEq inputs
      (by simpa only [boundary.depths,List.nil_append] using bufferEq) boundary.targets futureTables tableEq
      (gate stack) (by rw [endEq]; omega) live callback
  · have beforeDead := Bool.eq_false_iff.mpr live
    obtain ⟨rfl,budget,buffer,collectedEq,bufferEq⟩ := compiler_table_source_wasm1 ops law before collected st out data
      actual common depths fallback endPos encoded read
    subst collected
    obtain ⟨fixed,codeEq,_,frames,_,_,sources,cursor⟩ := compiler_br_table_dead_effect ops law
      {before with budget,table_depths := buffer} after out actual (Control.resultView common) beforeDead callback
    have ordinary : CompilerOrdinaryStable before after := by
      refine ⟨?_,fixed.stable.capacity⟩
      change (compilerMetadata after,after.frames,after.function.controls)=
        (compilerMetadata before,before.frames,before.function.controls)
      rw [fixed.stable.metadata,frames,fixed.controls]
      rfl
    exact invariant.skip (BrTable.instruction depths actual) beforeDead dead ordinary codeEq sources
      (by rw [endEq]; omega) (by rw [cursor])
end Exec.Code
