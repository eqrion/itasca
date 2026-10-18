import Exec.Code.Body.Control.Common.StructuredCoreEmbedding
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Float.ReaderFloatConstantPrefix
import Exec.Code.Body.Reader.Float.ReaderFloatConstantDead
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerStateWasm1.float32 {A : Type}
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
    (byte : data.val[st.pos.val]'inbounds = 67#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 67#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float32_wasm1 p ops law initial before after out C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float32_wasm1 p ops law initial before after out
      state.compiled live (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm1.float64 {A : Type}
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
    (byte : data.val[st.pos.val]'inbounds = 68#u8)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {st with pos := next} data env ctx 68#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm1 emit initial after types functions returns locals data env ctx bodyBt out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float64_wasm1 p ops law initial before after out C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float64_wasm1 p ops law initial before after out
      state.compiled live (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.float32 {A : Type}
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
    (byte : data.val[st.core.pos.val]'inbounds = 67#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 67#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float32_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f32]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float32_wasm2 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F32_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f32]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.float64 {A : Type}
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
    (byte : data.val[st.core.pos.val]'inbounds = 68#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 68#u8 before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨value, post, compiled⟩ := reader_prefix_float64_wasm2 p ops law initial before after out ctx rfl C
      contextCodeLocals state.compiled live sourceBound bodyBound (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f64]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨value, post, compiled, dead⟩ := reader_prefix_dead_float64_wasm2 p ops law initial before after out ctx rfl
      state.compiled live (by simpa only [p, ReaderBoundaryWasm1.pending, ReaderBoundaryWasm2.pending, global_simps] using byte) (by simpa only [code.OP_F64_CONST] using accepted)
    exact (state.advance next advance inbounds post (by simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices, ScalarConst.f64]) compiled (by simp [dead])).point

end Exec.Code
