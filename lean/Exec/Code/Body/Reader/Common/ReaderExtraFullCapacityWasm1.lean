import Exec.Code.Body.Reader.Common.ReaderCoreFullCapacityWasm1
import Exec.Code.Body.Reader.Common.StructuredReaderCompilerExtra
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_core_extra_full_capacity_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (opcode : U8) (covered : opcode.val ∈ [27,35,36,67,68,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62])
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    CapacityStep before after out := by

  simp only [List.mem_cons,List.mem_nil_iff,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h

  · have equal : opcode = 27#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_select_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · have equal : opcode = 35#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_global_get_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · have equal : opcode = 36#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_global_set_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · have equal : opcode = 67#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_f32_const_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · have equal : opcode = 68#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    exact reader_f64_const_full_capacity_wasm1 ops law before after st out data env ctx accepted
  · have equal : opcode = 40#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I32)) = 40#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.full .I32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 41#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .I64)) = 41#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.full .I64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 42#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F32)) = 42#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.full .F32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 43#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.full .F64)) = 43#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.full .F64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 44#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .S)) = 44#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I32 .byte .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 45#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .byte .U)) = 45#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I32 .byte .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 46#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .S)) = 46#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I32 .half .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 47#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I32 .half .U)) = 47#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I32 .half .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 48#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .S)) = 48#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .byte .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 49#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .byte .U)) = 49#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .byte .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 50#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .S)) = 50#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .half .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 51#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .half .U)) = 51#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .half .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 52#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .S)) = 52#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .word .S) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 53#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryLoadOpcode (.packed .I64 .word .U)) = 53#u8 := rfl
    exact reader_memory_load_full_capacity_wasm1 p ops law before after out (.packed .I64 .word .U) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 54#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I32)) = 54#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.full .I32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 55#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .I64)) = 55#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.full .I64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 56#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F32)) = 56#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.full .F32) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 57#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.full .F64)) = 57#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.full .F64) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 58#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .byte)) = 58#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.packed .I32 .byte) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 59#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I32 .half)) = 59#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.packed .I32 .half) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 60#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .byte)) = 60#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.packed .I64 .byte) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 61#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .half)) = 61#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.packed .I64 .half) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
  · have equal : opcode = 62#u8 := (UScalar.eq_equiv _ _).mpr h
    rw [equal] at byte accepted
    have exactOpcode : UScalar.cast .U8 (memoryStoreOpcode (.packed .I64 .word)) = 62#u8 := rfl
    exact reader_memory_store_full_capacity_wasm1 p ops law before after out (.packed .I64 .word) (by simpa only [exactOpcode] using byte) (by simpa only [exactOpcode] using accepted)
end Exec.Code
