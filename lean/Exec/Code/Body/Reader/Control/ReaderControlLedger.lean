import Exec.Code.Body.Reader.Table.ReaderTableLedger
import Exec.Code.Body.Reader.Common.ReaderOrdinaryEffects
import Exec.Code.Body.Reader.Control.ReaderReturn
import Exec.Code.Body.Reader.Control.ReaderControlEffects
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_control_ledger_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32) (opcode : U8)
    (covered : opcode.val ∈ [2,3,4,5,11,12,13,14,15])
    (budget : FixupBudget before.frames.val before.function.code.val.length)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
    AuxiliaryGrowth before after ∧ FixupBudget after.frames.val after.function.code.val.length := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at covered
  rcases covered with h | h | h | h | h | h | h | h | h
  · obtain rfl : opcode = 2#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 3#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 4#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 5#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 11#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 12#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 13#u8 := UScalar.eq_of_val_eq h
    have effects := reader_control_effects_wasm2 ops law before after st out data env ctx index _ (by first | exact .inl (by unfold ScopeOpcode; decide) | exact .inr (.inl rfl) | exact .inr (.inr rfl)) accepted
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
  · obtain rfl : opcode = 14#u8 := UScalar.eq_of_val_eq h
    exact reader_table_ledger_wasm2 ops law before after st out data env ctx index budget (by simpa only [global_simps] using accepted)
  · obtain rfl : opcode = 15#u8 := UScalar.eq_of_val_eq h
    have effects := reader_return_effects_wasm2 ops law before after st out data env ctx index (by simpa only [global_simps] using accepted)
    exact ⟨effects.auxiliary_growth, effects.fixups budget⟩
end Exec.Code
