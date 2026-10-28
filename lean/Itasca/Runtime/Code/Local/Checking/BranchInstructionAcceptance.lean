import Itasca.Runtime.Code.Local.Checking.OpenInstructionCompiler
import Itasca.Runtime.Code.Local.Control.Common.Structured

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A branch's overlap-safe copy fits from the independently checked source
and destination regions. Scalar/two-word copies are specialized by the runtime. -/
theorem transfer_instruction_accepts (function : runtime.bytecode.CompiledFunction)
    (dst src count : U32) (order : dst.val ≤ src.val)
    (source : src.val+count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (transferInstruction dst src count) = .ok true := by
  unfold transferInstruction
  split
  · rename_i one
    exact (CoreInstructionBounds.copy (by omega) (by omega)).accepts
  · split
    · rename_i two
      exact (CoreInstructionBounds.copy2 (by omega) (by omega)).accepts
    · exact (CoreInstructionBounds.copyN (by omega) source order).accepts

/-- Every word in an unconditional branch fragment checks, with only the final
jump allowed to wait for its recorded control-frame owner. -/
theorem branchInstructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchInstructions dst src count target).length-1)) :
    ∀ index instruction, (branchInstructions dst src count target)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .jump ready
    | succ index => simp [branchInstructions,elided] at found
  · simp only [branchInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : transferInstruction dst src count = instruction := by simpa [branchInstructions,elided] using found
      rw [← same]
      exact .checked (transfer_instruction_accepts function dst src count order source)
    | succ index =>
      cases index with
      | zero =>
        have same : .Jump target = instruction := by simpa [branchInstructions,elided] using found
        rw [← same]
        apply OpenInstructionCheck.jump
        simpa only [Nat.reduceAdd,show start+2-1 = start+1 by omega] using ready
      | succ index => simp [branchInstructions,elided] at found

/-- Conditional branch fragments check the selector and transfer immediately;
only their selected label target may remain pending. The skip address already
names the fragment's continuation. -/
theorem branchIfInstructions_open_checks (function : runtime.bytecode.CompiledFunction)
    (pending : Nat → Prop) (start : Nat) (dst src count target condition resume : U32)
    (order : dst.val ≤ src.val) (source : src.val+count.val ≤ function.slot_count.val)
    (test : condition.val+1 ≤ function.slot_count.val)
    (continuation : ¬ (count = 0#u32 ∨ src = dst) → resume.val ≤ function.code.length)
    (ready : target.val ≤ function.code.length ∨ pending (start+(branchIfInstructions dst src count target condition resume).length-1)) :
    ∀ index instruction, (branchIfInstructions dst src count target condition resume)[index]? = some instruction →
      OpenInstructionCheck function pending (start+index) instruction := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simp only [branchIfInstructions,if_pos elided,List.length_singleton,Nat.add_sub_cancel] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfNonZero condition target = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same,Nat.add_zero]
      exact .nonzero test ready
    | succ index => simp [branchIfInstructions,elided] at found
  · simp only [branchIfInstructions,if_neg elided,List.length_cons,List.length_nil] at ready
    intro index instruction found
    cases index with
    | zero =>
      have same : .JumpIfZero condition resume = instruction := by simpa [branchIfInstructions,elided] using found
      rw [← same]
      exact .zero test (.inl (continuation elided))
    | succ index =>
      cases index with
      | zero =>
        have same : transferInstruction dst src count = instruction := by simpa [branchIfInstructions,elided] using found
        rw [← same]
        exact .checked (transfer_instruction_accepts function dst src count order source)
      | succ index =>
        cases index with
        | zero =>
          have same : .Jump target = instruction := by simpa [branchIfInstructions,elided] using found
          rw [← same]
          apply OpenInstructionCheck.jump
          simpa only [Nat.reduceAdd,show start+3-1 = start+2 by omega] using ready
        | succ index => simp [branchIfInstructions,elided] at found

end Itasca.Runtime.Code
