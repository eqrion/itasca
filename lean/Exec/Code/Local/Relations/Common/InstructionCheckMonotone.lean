import Exec.Code.Local.Relations.Common.SimdInstructionAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Capacity and table lengths used by the bytecode checker only increase
while compiling the rest of a function. Contents are irrelevant to this local
check; their semantic correspondence is tracked by the executable relation. -/
structure InstructionCheckExtends (before after : runtime.bytecode.CompiledFunction) : Prop where
  slots : before.slot_count.val ≤ after.slot_count.val
  code : before.code.length ≤ after.code.length
  indirect : before.indirect.length ≤ after.indirect.length
  simd : before.simd.length ≤ after.simd.length
  constants : before.v128_pool.length ≤ after.v128_pool.length
  targets : before.jump_tables.length ≤ after.jump_tables.length

private theorem slots_fit_arithmetic (function : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit function start count =
      .ok (decide (start.val+count.val ≤ function.slot_count.val)) := by
  obtain ⟨result,called,exactBound⟩ := WP.spec_imp_exists (slots_fit_spec function start count)
  rw [called]
  congr 1
  cases result <;> simp_all

private theorem checked_difference_monotone (before after start count : Usize)
    (growth : before.val ≤ after.val)
    (accepted : (do let remaining ← before-start; Result.ok (decide (count ≤ remaining))) = .ok true) :
    (do let remaining ← after-start; Result.ok (decide (count ≤ remaining))) = .ok true := by
  obtain ⟨remaining,subtracted,returned⟩ := bind_ok_inv _ _ _ accepted
  have arithmetic := UScalar.sub_equiv before start
  rw [subtracted] at arithmetic
  simp at arithmetic
  have fits : count ≤ remaining := by simpa only [Result.ok.injEq,decide_eq_true_eq] using returned
  have checked : (do let rest ← after-start; Result.ok (decide (count ≤ rest))) ⦃ result => result = true ⦄ := by
    step as ⟨rest,restEq⟩
    simp only [WP.spec_ok,decide_eq_true_eq]
    scalar_tac
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists checked
  exact called

private theorem non_simd_instruction_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (noSimd : runtime.bytecode.Instr.simd instruction = .ok none)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  obtain ⟨slots,code,indirect,simd,constants,targets⟩ := growth
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,reduceCtorEq] at noSimd
  all_goals simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,
    runtime.bytecode.Instr.simd,slots_fit_arithmetic,bind_ok,lift,uncurry_apply_pair] at accepted ⊢
  all_goals simp_all only [bind_ok,ite_true,ite_false,Result.ok.injEq,decide_eq_true_eq]
  all_goals try dsimp only at accepted ⊢
  all_goals try split_ifs at accepted
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]
  all_goals try split_ifs
  all_goals try simp_all only [Result.ok.injEq,decide_eq_true_eq,Bool.false_eq_true]
  all_goals first | scalar_tac | exact checked_difference_monotone _ _ _ _ (by simpa using targets) accepted

/-- Every earlier instruction check remains valid as code, slot capacity, and
function-local metadata tables grow. Branch patching itself is handled
separately because it changes the stored instruction. -/
theorem instruction_valid_monotone (before after : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (growth : InstructionCheckExtends before after)
    (accepted : runtime.bytecode.CompiledFunction.instruction_valid before instruction = .ok true) :
    runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true := by
  have total : ∃ view, runtime.bytecode.Instr.simd instruction = .ok view := by
    cases instruction <;> exact ⟨_,rfl⟩
  obtain ⟨view,projected⟩ := total
  cases view with
  | none => exact non_simd_instruction_monotone before after instruction growth projected accepted
  | some view =>
    obtain ⟨opcode,dst,input,entry⟩ := view
    exact simd_instruction_monotone before after instruction opcode dst input entry projected growth.slots growth.simd accepted

end Exec.Code
