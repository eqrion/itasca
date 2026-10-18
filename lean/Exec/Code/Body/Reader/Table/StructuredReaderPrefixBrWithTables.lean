import Exec.Code.Body.Control.Table.StructuredCompilerPrefixBrWithTables
import Exec.Code.Body.Reader.Common.ReaderPostConcrete
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Body.Reader.Control.ReaderBranchWasm1
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br_wasm2_with_tables {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, ReaderPostWasm2 p out.core (.BR (.mk_uN depth.val)) true [] ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨depth, view, callback, read, post⟩ := reader_br_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input⟩ := reader_br_layout_wasm2 p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_live ops law out.core consumed reachable depth view scope selected discarded input callback
  · exact invariant.br_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

theorem structured_reader_prefix_br_wasm1_with_tables {jumpTables : List U32} {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BR)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BR before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, ReaderPostWasm1 p out (.BR (.mk_uN depth.val)) true [] ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR (.mk_uN depth.val)))
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨depth, resultBt, callback, read, post⟩ := reader_br_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input⟩ := reader_br_layout_wasm1 p same fronts (invariant.known reachable)
      (monomorphic reachable) depth resultBt out read
    exact invariant.br_live ops law out consumed reachable depth (Control.resultView resultBt) scope selected discarded input callback
  · exact invariant.br_dead ops law out consumed (Bool.eq_false_iff.mpr reachable) depth (Control.resultView resultBt) callback
end Exec.Code
