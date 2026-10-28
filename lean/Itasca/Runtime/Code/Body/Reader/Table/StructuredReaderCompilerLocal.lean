import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderCompilerState
import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderPrefixLocal
import Itasca.Runtime.Code.Body.Reader.Table.StructuredReaderPrefixDeadLocal
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.local_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_GET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_GET (.mk_uN localIndex.val))) (.LOCAL_GET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_get_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.local_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_SET (.mk_uN localIndex.val))) (.LOCAL_SET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_set_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem StructuredReaderCompilerStateWasm2.local_tee {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (embedding : LinearEmbedding locals emit)
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_TEE (.mk_uN localIndex.val))) (.LOCAL_TEE (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := structured_reader_prefix_local_tee_wasm2 p ops law initial before after out ctx rfl
      embedding state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := structured_reader_prefix_dead_local_tee_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Itasca.Runtime.Code
