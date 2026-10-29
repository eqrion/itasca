import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixAdvance
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredLinearEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState
import Itasca.Runtime.Compiler.Body.Reader.Scalar.DeadBasicPrefix

/-!
Nop/drop source prefixes and their structured compiler-state composition.
-/

/-! ## Structured Reader Prefix Empty -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem structured_reader_prefix_nop_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    ReaderPostWasm2 p out.core .NOP p.current.ctrl.polymorphic_base p.current.vals ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .NOP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨rawTypes, concrete⟩ := (concreteStack_iff _).mp (invariant.known reachable)
  have decoded := (SourceStack.of_map rawTypes concrete rfl).decoded
  have layout : CompilerLayout before (rawTypes.map Translate.valueType) := decoded ▸ retained.layout
  obtain ⟨ordinary, sources, cursor, post, lower, emission⟩ :=
    reader_emit_nop_wasm2 p ops law before after out ctx contextLocals rawTypes concrete layout byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨post, invariant.ordinary_empty_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, decoded] using emission
  · rw [cursor]

theorem structured_reader_prefix_drop_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState)
    (ctx : code.Context) (contextLocals : ctx.locals = sourceLocals)
    {emit types functions returns locals parents current}
    (embedding : LinearEmbedding locals emit)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.core.vals.val p.start.val)
    (reachable : before.reachable = true) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values,
      ReaderPostWasm2 p out.core .DROP p.current.ctrl.polymorphic_base values ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance .DROP)
        out.core.vals.val out.core.pos.val := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨ordinary, sources, cursor, front, ty, values, inputTypes, post, lower, emission⟩ :=
    reader_emit_drop_wasm2 p ops law before after out ctx contextLocals (invariant.known reachable) monomorphic retained.layout
      byte accepted
  have consumed : p.start.val < out.core.pos.val := by have pos := p.pos; have span := post.span; omega
  refine ⟨values, post, invariant.ordinary_empty_linear embedding reachable ordinary lower ?_ sources consumed ?_⟩
  · simpa only [retained.localsEq, inputTypes] using emission
  · rw [cursor]

end Itasca.Runtime.Code

end

/-! ## Structured Reader Compiler Empty -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.nop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.NOP)) savedParents
      (savedCurrent.advance (.plain (.NOP)) (.NOP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨post, compiled⟩ := structured_reader_prefix_nop_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_dead_nop_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.drop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.DROP)) savedParents
      (savedCurrent.advance (.plain (.DROP)) (.DROP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_drop_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled reach (state.reach.current reach) byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_drop_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Runtime.Code

end
