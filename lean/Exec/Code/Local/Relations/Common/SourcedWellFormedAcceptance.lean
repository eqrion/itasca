import Exec.Code.Local.Relations.Common.SourceWellFormedAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std

/-- The actual sourced instruction pass accepts from monotone, in-range
source coordinates and the local validity of each stored instruction. -/
theorem check_sourced_instructions_accepts (function : runtime.bytecode.CompiledFunction)
    (length index : Usize) (codeLength : length.val = function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (inside : index.val ≤ length.val)
    (coordinates : ∀ (j : Nat) (bound : j < function.source_offsets.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val ∧
      (0 < j → (function.source_offsets.val[j-1]'(by have bounded : j < function.source_offsets.val.length := bound; omega)).val ≤ function.source_offsets.val[j].val))
    (valid : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true) :
    checkInstructions function length false true index ⦃ result => result = true ⦄ := by
  exact check_source_instructions_accepts function length index codeLength sourceLength inside
    (fun j bound => ⟨(coordinates j bound).1,(coordinates j bound).2.1⟩)
    (fun j positive bound => (coordinates j bound).2.2 positive) valid

/-- Acceptance direction of the complete sourced publication checker. The
premises expose the local instruction, source-coordinate, target, and control
range obligations separately, for preservation through actual compilation. -/
theorem well_formed_sourced_accepts (function : runtime.bytecode.CompiledFunction)
    (nonsynthetic : ¬ (function.body_start = 0#usize ∧ function.body_end = 0#usize))
    (nonempty : 0 < function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (locals : function.local_slots.val ≤ function.slot_count.val)
    (params : function.param_slots.val ≤ function.local_slots.val)
    (returnStart returnCount : U32)
    (last : function.code.val[function.code.length-1]? = some (.Return returnStart returnCount))
    (instructions : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true)
    (coordinates : ∀ (j : Nat) (bound : j < function.source_offsets.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val ∧
      (0 < j → (function.source_offsets.val[j-1]'(by have bounded : j < function.source_offsets.val.length := bound; omega)).val ≤ function.source_offsets.val[j].val))
    (targets : ∀ entry ∈ function.jump_tables.val, entry.val < function.code.length)
    (ranges : ∀ entry ∈ function.controls.val,
      entry.start_pc.val ≤ entry.end_pc.val ∧ entry.end_pc.val < function.code.length ∧
      function.body_start.val ≤ entry.source_start.val ∧ entry.source_end.val ≤ function.body_end.val ∧
      entry.source_start.val < entry.source_end.val) :
    runtime.bytecode.CompiledFunction.well_formed function ⦃ result => result = true ⦄ := by
  have sourced : (if function.body_start = 0#usize then Result.ok (decide (function.body_end = 0#usize)) else Result.ok false : Result Bool) = Result.ok false := by
    by_cases first : function.body_start = 0#usize
    · have last : function.body_end ≠ 0#usize := by tauto
      simp [first,last]
    · simp [first]
  have notEmpty : alloc.vec.Vec.len function.code ≠ 0#usize := by scalar_tac
  have equalLength : alloc.vec.Vec.len function.source_offsets = alloc.vec.Vec.len function.code :=
    UScalar.eq_of_val_eq sourceLength
  have notLocals : ¬ function.local_slots > function.slot_count := by scalar_tac
  have notParams : ¬ function.param_slots > function.local_slots := by scalar_tac
  unfold runtime.bytecode.CompiledFunction.well_formed
  rw [sourced]
  simp [notEmpty,equalLength,notLocals,notParams]
  step as ⟨index,indexEq⟩
  have indexValue : index.val = function.code.length-1 := by scalar_tac
  have atCode : index.val < function.code.length := by omega
  step as ⟨instruction,found⟩
  have selected : instruction = .Return returnStart returnCount := by
    have atLast : function.code.val[index.val]? = some instruction := by
      simp [List.getElem?_eq_getElem atCode,found]
    rw [indexValue,last] at atLast
    exact (Option.some.inj atLast).symm
  rw [selected]
  simp only [runtime.bytecode.is_return,bind_ok,↓reduceIte]
  change (do
    let valid ← checkInstructions function (alloc.vec.Vec.len function.code) false true 0#usize
    let valid' ← runtime.bytecode.CompiledFunction.well_formed_loop1 function.jump_tables (alloc.vec.Vec.len function.code) valid 0#usize
    runtime.bytecode.CompiledFunction.well_formed_loop2 function.controls function.body_start function.body_end
      (alloc.vec.Vec.len function.code) valid' 0#usize) ⦃ result => result = true ⦄
  step with check_sourced_instructions_accepts function (alloc.vec.Vec.len function.code) 0#usize rfl sourceLength
    (by scalar_tac) coordinates instructions as ⟨checked,accepted⟩
  rw [accepted]
  step with check_jump_tables_accepts function.jump_tables (alloc.vec.Vec.len function.code) 0#usize
    (by scalar_tac) targets as ⟨checked,accepted⟩
  rw [accepted]
  apply check_control_maps_accepts function.controls function.body_start function.body_end
    (alloc.vec.Vec.len function.code) 0#usize (by scalar_tac) ranges

end Exec.Code
