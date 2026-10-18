import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPointWithTables
import Exec.Code.Body.Reader.Table.ReaderPrefixCoreBasicWithTables
import Exec.Code.Body.Reader.Table.ReaderPrefixDeadCoreBasicWithTables
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWithTablesWasm1.global_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 35#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm1 jumpTables emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get_wasm1_with_tables p ops law initial before after out C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get_wasm1_with_tables p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWithTablesWasm1.global_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 36#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm1 jumpTables emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set_wasm1_with_tables p ops law initial before after out C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set_wasm1_with_tables p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWithTablesWasm1.select {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx bodyBt st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm1 jumpTables emit initial before types functions returns locals data env ctx bodyBt st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.pos.val + 1) (inbounds : st.pos.val < data.length)
    (out : code.OpIterState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.pos.val]'inbounds = 27#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm1 jumpTables emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select_wasm1_with_tables p ops law initial before after out C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select_wasm1_with_tables p ops law initial before after out
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWithTablesWasm2.global_get {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 35#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 35#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_get_wasm2_with_tables p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_get_wasm2_with_tables p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_GET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWithTablesWasm2.global_set {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 36#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 36#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨idx, values, post, compiled⟩ := reader_prefix_global_set_wasm2_with_tables p ops law initial before after out ctx rfl C
      contextCodeLocals contextGlobals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨idx, values, post, compiled, dead⟩ := reader_prefix_dead_global_set_wasm2_with_tables p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_GLOBAL_SET] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWithTablesWasm2.select {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [CoreEmbedding C emit]
    (state : StructuredReaderCompilerStateWithTablesWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (contextCodeLocals : C.LOCALS = locals)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 27#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 27#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWithTablesWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨values, post, compiled⟩ := reader_prefix_select_wasm2_with_tables p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live (state.reach.current live) sourceBound bodyBound byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨values, post, compiled, dead⟩ := reader_prefix_dead_select_wasm2_with_tables p ops law initial before after out ctx rfl
      state.compiled live byte (by simpa only [code.OP_SELECT] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Exec.Code
