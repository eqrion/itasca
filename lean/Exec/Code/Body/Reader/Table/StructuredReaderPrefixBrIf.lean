import Exec.Code.Body.Control.Table.StructuredCompilerPrefixBrIf
import Exec.Code.Body.Reader.Control.ReaderBranchIfLayout
import Exec.Code.Body.Reader.Control.ReaderBranchWasm2
import Exec.Code.Local.Relations.Common.KnownPopStack
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_br_if_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[p.start.val]'p.inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType),
      ReaderPostWasm2 p out.core (.BR_IF (.mk_uN depth.val)) p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance (.BR_IF (.mk_uN depth.val)))
        out.core.vals.val out.core.pos.val ∧ after.reachable = before.reachable := by
  obtain ⟨depth, view, values, callback, read, post⟩ := reader_br_if_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨depth, values, post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨scope, discarded, selected, input, targetStack, known⟩ := reader_br_if_layout_wasm2 p same fronts (invariant.known reachable)
      (monomorphic reachable) depth view out read
    exact invariant.br_if_live ops law out.core known consumed reachable depth view scope selected discarded input targetStack
      ((Nat.le_of_lt p.inbounds).trans sourceBound) callback
  · exact invariant.br_if_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) depth view callback

end Exec.Code
