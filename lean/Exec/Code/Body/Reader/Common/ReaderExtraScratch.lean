import Exec.Code.Body.Reader.Common.ReaderCoreScratch
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerExtra
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_core_extra_depths_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (contextLocals : ctx.locals = locals)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    after.table_depths = before.table_depths := by

  simp only [List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h

  · have equal : opcode = 27#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_select_depths_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 35#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_global_get_depths_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 36#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_global_set_depths_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 67#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_f32_const_depths_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 68#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_f64_const_depths_wasm2 ops law before after st out data env ctx index accepted
  · have equal : opcode = 40#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I32)) = 40#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.full .I32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 41#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I64)) = 41#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.full .I64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 42#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F32)) = 42#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.full .F32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 43#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F64)) = 43#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.full .F64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 44#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .S)) = 44#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .byte .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 45#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .U)) = 45#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .byte .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 46#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .S)) = 46#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .half .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 47#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .U)) = 47#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .half .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 48#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .S)) = 48#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .byte .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 49#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .U)) = 49#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .byte .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 50#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .S)) = 50#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .half .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 51#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .U)) = 51#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .half .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 52#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .S)) = 52#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .word .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 53#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .U)) = 53#u8 := rfl
    exact reader_memory_load_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .word .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 54#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I32)) = 54#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.full .I32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 55#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I64)) = 55#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.full .I64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 56#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F32)) = 56#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.full .F32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 57#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F64)) = 57#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.full .F64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 58#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .byte)) = 58#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .byte) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 59#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .half)) = 59#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I32 .half) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 60#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .byte)) = 60#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .byte) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 61#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .half)) = 61#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .half) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 62#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .word)) = 62#u8 := rfl
    exact reader_memory_store_depths_wasm2 p ops law before after out ctx contextLocals (.packed .I64 .word) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
end Exec.Code
