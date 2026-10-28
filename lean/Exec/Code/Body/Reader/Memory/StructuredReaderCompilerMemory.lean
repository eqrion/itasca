import Exec.Code.Body.Control.Common.StructuredScalarEmbedding
import Exec.Code.Body.Reader.Table.StructuredReaderCompilerPoint
import Exec.Code.Body.Reader.Memory.ReaderPrefixMemory
import Exec.Code.Body.Reader.Memory.ReaderPrefixDeadMemory
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.memory_load {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Memory.Load)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (memoryLoadOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (memoryLoadOpcode op)) before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨arg,values,post,compiled⟩ := reader_prefix_memory_load_wasm2 p ops law initial before after out ctx rfl C
      contextLocals contextMemories state.compiled live (state.reach.current live) op sourceBound bodyBound byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Load.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨arg,values,post,compiled,dead⟩ := reader_prefix_dead_memory_load_wasm2 p ops law initial before after out ctx rfl
      state.compiled live op byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Load.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

theorem StructuredReaderCompilerStateWasm2.memory_store {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (op : Abs.Memory.Store)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = (UScalar.cast .U8 (memoryStoreOpcode op)))
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 (UScalar.cast .U8 (memoryStoreOpcode op)) before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases live : before.reachable with
  | true =>
    obtain ⟨arg,values,post,compiled⟩ := reader_prefix_memory_store_wasm2 p ops law initial before after out ctx rfl C
      contextLocals contextMemories state.compiled live (state.reach.current live) op sourceBound bodyBound byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Store.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (fun _ => state.reach.current live)).point
  | false =>
    obtain ⟨arg,values,post,compiled,dead⟩ := reader_prefix_dead_memory_store_wasm2 p ops law initial before after out ctx rfl
      state.compiled live op byte accepted
    exact (state.advance next advance inbounds post (by cases op <;> simp [Abs.Memory.Store.source, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) compiled (by simp [dead])).point

end Itasca.Runtime.Code