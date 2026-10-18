import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Common.ReaderPrefixCoreBasic
import Exec.Code.Body.Reader.Common.ReaderPrefixDeadCoreBasic
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWasm1.global_get {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 35#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get_wasm1 p ops law initial before after out C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get_wasm1 p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm1.global_set {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 36#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set_wasm1 p ops law initial before after out C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set_wasm1 p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm1.select {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm1 emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 27#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select_wasm1 p ops law initial before after out C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select_wasm1 p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.global_get {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.global_set {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.select {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select_wasm2 p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Exec.Code
