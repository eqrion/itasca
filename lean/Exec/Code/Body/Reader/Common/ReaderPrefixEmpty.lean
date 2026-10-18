import Exec.Code.Body.Callbacks.Common.CompilerPrefixAdvance
import Exec.Code.Body.Reader.Common.ReaderEmpty
import Exec.Code.Body.Reader.Common.ReaderSpan
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_prefix_nop_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    ReaderPostWasm2 p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .NOP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp invariant.known
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  obtain ⟨ordinary, sources, cursor, post, lower, emission⟩ :=
    reader_emit_nop_wasm2 p ops law before after out ctx contextLocals rawTypes concrete layout byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨post, invariant.ordinary_empty reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem reader_prefix_drop_wasm2 {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .DROP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨ordinary, sources, cursor, front, ty, values, inputTypes, post, lower, emission⟩ :=
    reader_emit_drop_wasm2 p ops law before after out ctx contextLocals invariant.known monomorphic retained.layout
      byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_empty reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

theorem reader_prefix_nop_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (reachable : before.reachable = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_NOP before = .ok (.Ok (), out, after)) :
    ReaderPostWasm1 p out .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .NOP)
        out.vals.val out.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp invariant.known
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  obtain ⟨ordinary, sources, cursor, post, lower, emission⟩ :=
    reader_emit_nop_wasm1 p ops law before after out rawTypes concrete layout byte accepted
  have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨post, invariant.ordinary_empty reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem reader_prefix_drop_wasm1 {data env ctx bt st}
    (p : Wasm1.Pending data env ctx bt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    {types functions returns locals parents current}
    (invariant : CompilerPrefix initial before types functions returns locals parents current st.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm1 p out .DROP p.current.ctrl.polymorphic_base values ∧
      CompilerPrefix initial after types functions returns locals parents (current.advance .DROP)
        out.vals.val out.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨ordinary, sources, cursor, front, ty, values, inputTypes, post, lower, emission⟩ :=
    reader_emit_drop_wasm1 p ops law before after out invariant.known monomorphic retained.layout
      byte accepted
  have consumed : p.start.val < out.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_empty reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Exec.Code
