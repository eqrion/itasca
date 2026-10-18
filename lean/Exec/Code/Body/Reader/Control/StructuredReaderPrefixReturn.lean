import Exec.Code.Body.Control.Control.StructuredCompilerPrefixReturn
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Control.ReaderReturnStack
import Exec.Code.Body.Reader.Common.ReaderRootFrame
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_return_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions (p.ft.results.val.map Translate.valueType)
      locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 15#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 15#u8 before = .ok (.Ok (), out, after)) :
    ReaderPostWasm2 p out.core .RETURN true [] ∧
      StructuredCompilerPrefix emit initial after types functions (p.ft.results.val.map Translate.valueType)
        locals parents (current.advance .RETURN) out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm2 p before invariant.frames same
    obtain ⟨_, outer, _, _, base, _, controls, _, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm2 st out env index p.ft.results.val outer p.current.vals
      (by simp [Wasm2.resolve, p.signature]) vals (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact invariant.return_live ops law out.core consumed reachable frame found resultWidth front input
      codeFits sourceFits coordinateFits callback
  · exact invariant.return_dead ops law out.core consumed (Bool.eq_false_iff.mpr reachable) callback

theorem structured_reader_prefix_return_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {emit types functions locals parents current}
    (invariant : StructuredCompilerPrefix emit initial before types functions (ctx.results.val.map Translate.valueType)
      locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (bodyResults : Control.resultTypes bt = ctx.results.val.map Translate.valueType)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_RETURN)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_RETURN before = .ok (.Ok (), out, after)) :
    ReaderPostWasm1 p out .RETURN true [] ∧
      StructuredCompilerPrefix emit initial after types functions (ctx.results.val.map Translate.valueType)
        locals parents (current.advance .RETURN) out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨callback, read, values, post⟩ := reader_return_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  refine ⟨post, ?_⟩
  by_cases reachable : before.reachable = true
  · obtain ⟨frame, found, resultWidth⟩ := reader_root_frame_wasm1 p before invariant.frames same
    rw [bodyResults] at resultWidth
    obtain ⟨_, outer, _, _, base, _, controls, vals⟩ := p.opened
    obtain ⟨front, input⟩ := reader_return_stack_wasm1 st out ctx outer p.current.vals vals
      (by simpa [Control.base, controls] using base)
      (invariant.known reachable) (by simpa [Control.polymorphic, controls] using monomorphic reachable) read
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits, sourceFits, _, _⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    exact invariant.return_live ops law out consumed reachable frame found resultWidth front input
      codeFits sourceFits coordinateFits callback
  · exact invariant.return_dead ops law out consumed (Bool.eq_false_iff.mpr reachable) callback
end Exec.Code
