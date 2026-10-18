import Exec.Code.Local.Relations.Common.WellFormed
import Itasca.Support.Result

namespace Exec.Code
open Aeneas Aeneas.Std Itasca.ResultFacts

@[step] theorem slots_fit_spec (f : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit f start count
      ⦃ out => out = true ↔ start.val + count.val ≤ f.slot_count.val ⦄ := by
  unfold runtime.bytecode.CompiledFunction.slots_fit
  split
  · step as ⟨remaining, hremaining⟩
    simp only [decide_eq_true_eq]
    scalar_tac
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    scalar_tac

theorem slots_fit_true (f : runtime.bytecode.CompiledFunction) (start count : U32)
    (checked : runtime.bytecode.CompiledFunction.slots_fit f start count = .ok true) :
    start.val + count.val ≤ f.slot_count.val := by
  have correct := slots_fit_spec f start count
  rw [checked] at correct
  simp only [WP.spec_ok, true_iff] at correct
  exact correct

/-- Scalar dispatch reads and writes only slots validated by the independent
bytecode checker. -/
theorem scalar_valid_bounds (f : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (op : U16) (dst a b : U32)
    (shape : runtime.bytecode.Instr.scalar instruction = .ok (some (op, dst, a, b)))
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f instruction = .ok true) :
    dst.val < f.slot_count.val ∧ a.val < f.slot_count.val ∧ b.val < f.slot_count.val := by
  unfold runtime.bytecode.CompiledFunction.instruction_valid at checked
  rw [shape, bind_ok] at checked
  obtain ⟨destination, hd, checked⟩ := bind_ok_inv _ _ _ checked
  cases destination with
  | false => simp at checked
  | true =>
    simp only [ite_true] at checked
    obtain ⟨left, ha, checked⟩ := bind_ok_inv _ _ _ checked
    cases left with
    | false => simp at checked
    | true =>
      simp only [ite_true] at checked
      have bd := slots_fit_true f dst 1#u32 hd
      have ba := slots_fit_true f a 1#u32 ha
      have bb := slots_fit_true f b 1#u32 checked
      scalar_tac


private theorem checked_and (first second : Result Bool)
    (checked : (do let b ← first; if b then second else .ok false) = .ok true) :
    first = .ok true ∧ second = .ok true := by
  obtain ⟨value, firstRun, checked⟩ := bind_ok_inv _ _ _ checked
  cases value with
  | false => simp at checked
  | true => exact ⟨firstRun, checked⟩

theorem copy_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Copy dst src) = .ok true) :
    dst.val + 1 ≤ f.slot_count.val ∧ src.val + 1 ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨left, right⟩ := checked_and _ _ checked
  have dl := slots_fit_true f dst 1#u32 left
  have sl := slots_fit_true f src 1#u32 right
  scalar_tac

theorem copy2_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Copy2 dst src) = .ok true) :
    dst.val + 2 ≤ f.slot_count.val ∧ src.val + 2 ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨left, right⟩ := checked_and _ _ checked
  have dl := slots_fit_true f dst 2#u32 left
  have sl := slots_fit_true f src 2#u32 right
  scalar_tac

theorem const32_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst : U32) (value : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Const32 dst value) = .ok true) :
    dst.val < f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  have bound := slots_fit_true f dst 1#u32 checked
  scalar_tac

theorem const64_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst : U32) (value : U64)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Const64 dst value) = .ok true) :
    dst.val < f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  have bound := slots_fit_true f dst 1#u32 checked
  scalar_tac

theorem copyN_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst src count : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.CopyN dst src count) = .ok true) :
    dst.val ≤ src.val ∧ dst.val + count.val ≤ f.slot_count.val ∧ src.val + count.val ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  split at checked
  · obtain ⟨left, right⟩ := checked_and _ _ checked
    have dl := slots_fit_true f dst count left
    have sl := slots_fit_true f src count right
    scalar_tac
  · cases Result.ok_injective checked

theorem return_valid_bounds (f : runtime.bytecode.CompiledFunction) (src count : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Return src count) = .ok true) :
    src.val + count.val ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  exact slots_fit_true f src count checked

theorem call_valid_bounds (f : runtime.bytecode.CompiledFunction) (index base : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Call index base) = .ok true) :
    base.val ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  have bound := slots_fit_true f base 0#u32 checked
  scalar_tac

theorem jump_valid_bounds (f : runtime.bytecode.CompiledFunction) (target : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Jump target) = .ok true) :
    target.val < f.code.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  simp only [lift, bind_ok] at checked
  have bound := Result.ok_injective checked
  scalar_tac

theorem jumpIfZero_valid_bounds (f : runtime.bytecode.CompiledFunction) (cond target : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.JumpIfZero cond target) = .ok true) :
    cond.val < f.slot_count.val ∧ target.val < f.code.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨slot, targetRun⟩ := checked_and _ _ checked
  have bound := slots_fit_true f cond 1#u32 slot
  simp only [lift, bind_ok] at targetRun
  have targetBound := Result.ok_injective targetRun
  scalar_tac

theorem jumpIfNonZero_valid_bounds (f : runtime.bytecode.CompiledFunction) (cond target : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.JumpIfNonZero cond target) = .ok true) :
    cond.val < f.slot_count.val ∧ target.val < f.code.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨slot, targetRun⟩ := checked_and _ _ checked
  have bound := slots_fit_true f cond 1#u32 slot
  simp only [lift, bind_ok] at targetRun
  have targetBound := Result.ok_injective targetRun
  scalar_tac

end Exec.Code
