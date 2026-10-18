import Exec.Code.Body.Reader.Common.ReaderCompilerState
import Exec.Code.Body.Reader.Local.ReaderPrefixLocal
import Exec.Code.Body.Reader.Local.ReaderPrefixDeadLocal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem ReaderCompilerStateWasm1.local_get {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_LOCAL_GET)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.LOCAL_GET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_GET (.mk_uN localIndex.val))) (.LOCAL_GET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_get_wasm1 p ops law initial before after out
      state.compiled currentLocals reach sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_get_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm2.local_get {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_GET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_GET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_GET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_GET (.mk_uN localIndex.val))) (.LOCAL_GET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled currentLocals reach sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm1.local_set {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_LOCAL_SET)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_SET (.mk_uN localIndex.val))) (.LOCAL_SET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_set_wasm1 p ops law initial before after out
      state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_set_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm2.local_set {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_SET)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_SET before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_SET (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_SET (.mk_uN localIndex.val))) (.LOCAL_SET (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm1.local_tee {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm1 initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm1 initial after types functions returns locals data env ctx bodyBt out
      parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_TEE (.mk_uN localIndex.val))) (.LOCAL_TEE (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_tee_wasm1 p ops law initial before after out
      state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_tee_wasm1 p ops law initial before after out
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post compiled (by simp [dead])⟩

theorem ReaderCompilerStateWasm2.local_tee {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : ReaderCompilerStateWasm2 initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (localsMatch : initial.function.locals = ctx.locals)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOCAL_TEE)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOCAL_TEE before = .ok (.Ok (), out, after)) :
    ∃ (localIndex : U32) (values : List code.StackType), ReaderCompilerStateWasm2 initial after types functions returns locals data env ctx.locals index ft out
      parents (current.advance (.LOCAL_TEE (.mk_uN localIndex.val))) savedParents
      (savedCurrent.advance (.plain (.LOCAL_TEE (.mk_uN localIndex.val))) (.LOCAL_TEE (.mk_uN localIndex.val)) savedCurrent.ctrl.polymorphic_base values) := by
  let p := state.boundary.pending next advance inbounds
  have currentLocals : before.function.locals = ctx.locals := state.compiled.metadata.fields.2.2.2.2.1.trans localsMatch
  cases reach : before.reachable with
  | true =>
    obtain ⟨localIndex, values, post, compiled⟩ := reader_prefix_local_tee_wasm2 p ops law initial before after out ctx rfl
      state.compiled currentLocals reach (state.reach.current reach) sourceBound bodyBound byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current reach)⟩
  | false =>
    obtain ⟨localIndex, values, post, compiled, dead⟩ := reader_prefix_dead_local_tee_wasm2 p ops law initial before after out ctx rfl
      state.compiled reach byte accepted
    exact ⟨localIndex, values, state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])⟩

end Exec.Code
