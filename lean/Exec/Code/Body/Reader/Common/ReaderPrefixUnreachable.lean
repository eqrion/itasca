import Exec.Code.Body.Callbacks.Common.CompilerPrefixUnreachable
import Exec.Code.Body.Reader.Common.ReaderUnreachable
import Exec.Code.Body.Reader.Common.ReaderProfile
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_unreachable_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    ReaderPostWasm2 p out.core .UNREACHABLE true [] ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .UNREACHABLE)
        out.core.vals.val out.core.pos.val ∧ after.reachable = false := by
  obtain ⟨capacity, run⟩ := profile_base_success_wasm2
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx
    ⟨sourceLocals, p.ft.results⟩ index code.OP_UNREACHABLE before after
    (by simp only [global_simps]; decide) (by simp only [global_simps]; decide)
    (by simp only [global_simps]; rfl) (by simp only [global_simps]; decide) contextLocals accepted
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out.core byte run
  have known : ConcreteStack out.core.vals.val := values ▸ invariant.known.take _
  have consumed : p.start.val < out.core.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨post, invariant.unreachable ops law out.core known consumed callback⟩

theorem reader_prefix_unreachable_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_UNREACHABLE before = .ok (.Ok (), out, after)) :
    ReaderPostWasm1 p out .UNREACHABLE true [] ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .UNREACHABLE)
        out.vals.val out.pos.val ∧ after.reachable = false := by
  obtain ⟨callback, values, post⟩ := reader_unreachable_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  have known : ConcreteStack out.vals.val := values ▸ invariant.known.take _
  have consumed : p.start.val < out.pos.val := by have position := p.pos; have span := post.span; omega
  exact ⟨post, invariant.unreachable ops law out known consumed callback⟩

end Exec.Code
