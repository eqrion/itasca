import Exec.Code.Body.Reader.Common.ReaderNumericCapacity
import Exec.Code.Body.Reader.Common.ReaderSignCapacity
import Exec.Code.Body.Reader.Common.ReaderCapacity
import Exec.Code.Local.Relations.Common.SliceOpcodes
namespace Exec.Code
open Aeneas Aeneas.Std Itasca
/-- Successful source-reader dispatch increases capacity only as required by
its returned validator stack, for every opcode of the proved slice. -/
theorem reader_step_base_capacity_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (supported : SliceBaseOpcode opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  simp only [SliceBaseOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have equal : opcode = 0#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_unreachable_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 1#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_nop_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 2#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_block_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 3#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_loop_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 4#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_if_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 5#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_else_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 11#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_end_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 12#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_br_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 13#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_br_if_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 15#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_return_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 16#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_call_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 26#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_drop_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 32#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_local_get_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 33#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_local_set_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 34#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_local_tee_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 65#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_i32_const_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 66#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_i64_const_capacity ops law before after st out data env ctx (by simpa only [global_simps] using accepted)
  · have equal : opcode = 69#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_eqz_capacity ops law before after st out data env ctx .I32 accepted
  · have equal : opcode = 70#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I32 .eq accepted
  · have equal : opcode = 73#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I32 .ltU accepted
  · have equal : opcode = 80#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_eqz_capacity ops law before after st out data env ctx .I64 accepted
  · have equal : opcode = 81#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I64 .eq accepted
  · have equal : opcode = 84#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I64 .ltU accepted
  · have equal : opcode = 106#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I32 .add accepted
  · have equal : opcode = 107#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I32 .sub accepted
  · have equal : opcode = 124#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I64 .add accepted
  · have equal : opcode = 125#u8 := (UScalar.eq_equiv _ _).mpr h
    subst opcode
    exact reader_binary_capacity ops law before after st out data env ctx .I64 .sub accepted
theorem reader_step_capacity_wasm1 {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (opcode : U8) (supported : SliceOpcode opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (), out, after)) :
    CapacityStep before after out := by
  rcases supported.base_or_numeric with base | ⟨operation, rfl⟩
  · exact reader_step_base_capacity_wasm1 ops law before after st out data env ctx opcode base accepted
  · by_cases standard : (integerOpcode operation).val < 192
    · exact reader_numeric_capacity ops law before after st out data env ctx operation standard accepted
    · exact False.elim (reader_integer_sign_wasm1_impossible ops before after st out data env ctx operation (by omega) accepted)
end Exec.Code
