import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixEmpty
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixDeadBasic
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm1.nop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_NOP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_NOP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.NOP)) savedParents
      (savedCurrent.advance (.plain (.NOP)) (.NOP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨post, compiled⟩ := structured_reader_prefix_nop_wasm1 p ops law initial before after out
      embedding state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨post, compiled, dead⟩ := structured_reader_prefix_dead_nop_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨savedCurrent.vals, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.nop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_NOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_NOP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
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

theorem StructuredReaderCompilerStateWasm1.drop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (byte : data.val[st.pos.val]'inbounds = code.OP_DROP)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.DROP)) savedParents
      (savedCurrent.advance (.plain (.DROP)) (.DROP) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  cases reach : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := structured_reader_prefix_drop_wasm1 p ops law initial before after out
      embedding state.compiled reach (state.reach.current reach) byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := structured_reader_prefix_dead_drop_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨values, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.drop {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_DROP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_DROP before = .ok (.Ok (), out, after)) :
    ∃ values, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
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

end Exec.Code
