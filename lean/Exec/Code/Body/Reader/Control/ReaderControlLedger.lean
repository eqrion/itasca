import Exec.Code.Body.Reader.Table.ReaderTableLedger
import Exec.Code.Body.Reader.Control.ReaderControlFixupsWasm1
import Exec.Code.Body.Reader.Control.ReaderControlFixupsWasm2
import Exec.Code.Body.Reader.Control.ReaderControlAuxiliaryGrowth
import Exec.Code.Body.Reader.Table.ReaderOrdinaryTables
import Exec.Code.Body.Reader.Table.ReaderOrdinaryTablesWasm1
import Exec.Code.Body.Reader.Common.ReaderOrdinaryCodeMonotone
import Exec.Code.Body.Reader.Common.ReaderOrdinaryCodeMonotoneWasm1
import Exec.Code.Body.Reader.Control.ReaderReturn
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_control_ledger_wasm1 {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (out : code.OpIterState) (opcode : U8)
    (covered : opcode.val ∈ [2,3,4,5,11,12,13,14,15])
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_block_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_block_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_loop_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_loop_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_if_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_if_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 5#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_else_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_else_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 11#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_end_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_end_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_br_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_br_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_br_if_auxiliary_growth_wasm1 p ops law before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_br_if_fixup_budget_wasm1 p ops law before after out budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 14#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_table_ledger_wasm1 ops law before after st out data env ctx budget (by simpa only [global_simps] using accepted)
  · have equal : opcode = 15#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    obtain ⟨callback,_⟩ := reader_return_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact ⟨.of_tables (reader_return_tables_wasm1 ops law before after st out data env ctx
      (by simpa only [global_simps] using accepted))
      (reader_return_code_mono_wasm1 ops law before after st out data env ctx
      (by simpa only [global_simps] using accepted)),
      compiler_return_fixup_budget ops law before after out budget callback⟩

theorem reader_control_ledger_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (opcode : U8)
    (covered : opcode.val ∈ [2,3,4,5,11,12,13,14,15])
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h
  · have equal : opcode = 2#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_block_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_block_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 3#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_loop_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_loop_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 4#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_if_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_if_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 5#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_else_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_else_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 11#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_end_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_end_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 12#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_br_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_br_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 13#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact ⟨reader_br_if_auxiliary_growth_wasm2 p ops law before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted),
      reader_br_if_fixup_budget_wasm2 p ops law before after out ctx budget
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)⟩
  · have equal : opcode = 14#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    exact reader_table_ledger_wasm2 ops law before after st out data env ctx index budget (by simpa only [global_simps] using accepted)
  · have equal : opcode = 15#u8 := UScalar.eq_of_val_eq h
    rw [equal] at byte accepted
    obtain ⟨callback,_⟩ := reader_return_wasm2 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact ⟨.of_tables (reader_return_tables_wasm2 ops law before after st out data env ctx index
      (by simpa only [global_simps] using accepted))
      (reader_return_code_mono_wasm2 ops law before after st out data env ctx index
      (by simpa only [global_simps] using accepted)),
      compiler_return_fixup_budget ops law before after out.core budget callback⟩
end Exec.Code
