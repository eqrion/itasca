import Exec.Code.Body.Control.Common.StructuredScalarEmbedding
import Exec.Code.Body.Reader.Table.StructuredReaderCoreBasic
import Exec.Code.Body.Reader.Memory.StructuredReaderCompilerMemory
import Exec.Code.Body.Reader.Float.ReaderFloatConstantState
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.core_extra {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (C : context) {emit} [ScalarEmbedding C emit]
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st parents current savedParents savedCurrent)
    (contextLocals : C.LOCALS = locals)
    (contextGlobals : C.GLOBALS = env.global_types.val.map Translate.globalType)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h

  · have equal : opcode = 27#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.select ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 35#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.global_get ops law C contextLocals contextGlobals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 36#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.global_set ops law C contextLocals contextGlobals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 67#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.float32 ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 68#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact state.float64 ops law C contextLocals next advance inbounds out sourceBound bodyBound byte accepted
  · have equal : opcode = 40#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I32)) = 40#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .I32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 41#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I64)) = 41#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .I64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 42#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F32)) = 42#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .F32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 43#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F64)) = 43#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.full .F64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 44#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .S)) = 44#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 45#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .U)) = 45#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 46#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .S)) = 46#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 47#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .U)) = 47#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 48#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .S)) = 48#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 49#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .U)) = 49#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 50#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .S)) = 50#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 51#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .U)) = 51#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 52#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .S)) = 52#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word .S) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 53#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .U)) = 53#u8 := rfl
    exact state.memory_load ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word .U) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 54#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I32)) = 54#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .I32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 55#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I64)) = 55#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .I64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 56#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F32)) = 56#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .F32) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 57#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F64)) = 57#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.full .F64) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 58#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .byte)) = 58#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .byte) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 59#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .half)) = 59#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I32 .half) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 60#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .byte)) = 60#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .byte) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 61#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .half)) = 61#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .half) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 62#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .word)) = 62#u8 := rfl
    exact state.memory_store ops law C contextLocals contextMemories next advance inbounds out (.packed .I64 .word) sourceBound bodyBound (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
end Itasca.Runtime.Code