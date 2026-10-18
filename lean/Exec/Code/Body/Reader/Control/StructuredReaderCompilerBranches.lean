import Exec.Code.Body.Reader.Common.StructuredReaderCompilerState
import Exec.Code.Body.Reader.Common.StructuredReaderPrefixBr
import Exec.Code.Body.Reader.Control.StructuredReaderPrefixBrIf
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.br {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (byte : data.val[st.core.pos.val]'inbounds = 12#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 12#u8 before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR (.mk_uN depth.val))) (.BR (.mk_uN depth.val)) true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, post, compiled, dead⟩ := structured_reader_prefix_br_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current byte accepted
  exact ⟨depth, state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm1.br {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (byte : data.val[st.pos.val]'inbounds = code.OP_BR)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_BR before = .ok (.Ok (), out, after)) :
    ∃ depth : U32, StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.BR (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR (.mk_uN depth.val))) (.BR (.mk_uN depth.val)) true []) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, post, compiled, dead⟩ := structured_reader_prefix_br_wasm1 p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current byte accepted
  exact ⟨depth, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.br_if {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[st.core.pos.val]'inbounds = 13#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 13#u8 before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.BR_IF (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR_IF (.mk_uN depth.val))) (.BR_IF (.mk_uN depth.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, values, post, compiled, reach⟩ := structured_reader_prefix_br_if_wasm2 p ops law initial before after out ctx
    state.compiled state.sources state.fronts state.reach.current sourceBound byte accepted
  exact ⟨depth, values, state.advance next advance inbounds post
    (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reach.symm.trans live))⟩

theorem StructuredReaderCompilerStateWasm1.br_if {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (byte : data.val[st.pos.val]'inbounds = code.OP_BR_IF)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_BR_IF before = .ok (.Ok (), out, after)) :
    ∃ (depth : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm1 emit initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.BR_IF (.mk_uN depth.val))) savedParents
      (savedCurrent.advance (.plain (.BR_IF (.mk_uN depth.val))) (.BR_IF (.mk_uN depth.val))
        savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨depth, values, post, compiled, reach⟩ := structured_reader_prefix_br_if_wasm1 p ops law initial before after out
    state.compiled state.sources state.fronts state.reach.current sourceBound byte accepted
  exact ⟨depth, values, state.advance next advance inbounds post compiled
    (fun live => state.reach.current (reach.symm.trans live))⟩
end Exec.Code
