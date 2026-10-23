import Exec.Code.Local.Relations.Common.WellFormedAcceptance

namespace Exec.Code
open Aeneas Aeneas.Std

abbrev checkSourceCoordinate (function : runtime.bytecode.CompiledFunction) (index : Usize) : Result Bool := do
  let source ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) function.source_offsets index
  if source < function.body_start then .ok false
  else if source ≥ function.body_end then .ok false
  else if index > 0#usize then do
    let prior ← index - 1#usize
    let value ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Usize) function.source_offsets prior
    if value > source then .ok false else .ok true
  else .ok true

/-- The source-coordinate gate accepts a coordinate within the body and in
nondecreasing order with its predecessor. All premises are numeric bounds. -/
theorem source_coordinate_accepts (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val < function.source_offsets.val.length)
    (range : function.body_start.val ≤ function.source_offsets.val[index.val].val ∧
      function.source_offsets.val[index.val].val < function.body_end.val)
    (ordered : 0 < index.val →
      (function.source_offsets.val[index.val-1]'(by omega)).val ≤ function.source_offsets.val[index.val].val) :
    checkSourceCoordinate function index ⦃ result => result = true ⦄ := by
  unfold checkSourceCoordinate
  step as ⟨source,found⟩
  have beforeStart : ¬ source < function.body_start := by rw [found]; scalar_tac
  have afterEnd : ¬ source ≥ function.body_end := by rw [found]; scalar_tac
  simp only [if_neg beforeStart,if_neg afterEnd]
  split
  · rename_i positive
    step as ⟨prior,priorEq⟩
    have priorValue : prior.val = index.val - 1 := by scalar_tac
    step as ⟨value,valueEq⟩
    have comparison : ¬ value > source := by
      have sorted := ordered (by scalar_tac)
      rw [found,valueEq]
      have same : (function.source_offsets.val[prior.val]).val =
          (function.source_offsets.val[index.val-1]'(by omega)).val := by simp [priorValue]
      scalar_tac
    simp [comparison]
  · simp

/-- The ordinary-body instruction pass accepts independently bounded,
nondecreasing source coordinates and valid instruction operands. -/
theorem check_source_instructions_accepts (function : runtime.bytecode.CompiledFunction)
    (length index : Usize) (codeLength : length.val = function.code.length)
    (sourceLength : function.source_offsets.length = function.code.length)
    (inside : index.val ≤ length.val)
    (ranges : ∀ (j : Nat) (bound : j < function.source_offsets.val.length),
      function.body_start.val ≤ function.source_offsets.val[j].val ∧
      function.source_offsets.val[j].val < function.body_end.val)
    (ordered : ∀ (j : Nat) (positive : 0 < j) (bound : j < function.source_offsets.val.length),
      (function.source_offsets.val[j-1]'(by omega)).val ≤ function.source_offsets.val[j].val)
    (valid : ∀ (j : Nat) (bound : j < function.code.length),
      runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[j] = .ok true) :
    checkInstructions function length false true index ⦃ result => result = true ⦄ := by
  unfold checkInstructions runtime.bytecode.CompiledFunction.well_formed_loop0
  apply loop.spec_decr_nat (fun state => length.val - state.2.val)
    (fun state => state.1 = true ∧ state.2.val ≤ length.val)
  · rintro ⟨flag,current⟩ ⟨rfl,bounded⟩
    unfold runtime.bytecode.CompiledFunction.well_formed_loop0.body
    dsimp only
    split
    · rename_i more
      have atCode : current.val < function.code.length := by scalar_tac
      have atSource : current.val < function.source_offsets.val.length := by
        change current.val < function.source_offsets.length
        omega
      simp only [↓reduceIte,Bool.false_eq_true,if_false]
      apply WP.spec_bind (source_coordinate_accepts function current atSource (ranges _ atSource)
        (fun positive => ordered _ positive atSource))
      intro checked accepted
      rw [accepted]
      step as ⟨instruction,foundInstruction⟩
      rw [foundInstruction,valid current.val atCode]
      simp only [↓reduceIte,bind_ok]
      step as ⟨next,advanced⟩
      all_goals scalar_tac
    · simp
  · exact ⟨rfl,inside⟩

end Exec.Code
