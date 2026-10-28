import Exec.Code.Local.Checking.OpenInstructionCompiler
import Exec.Code.Local.Callbacks.Common.FixupAlgebra

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Patching a branch to the current exit replaces its outstanding target
obligation. Condition operands retain their existing slot bounds. -/
theorem OpenInstructionCheck.retarget {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (target : U32)
    (inside : target.val ≤ after.code.length) :
    OpenInstructionCheck after next index (retarget instruction target) := by
  cases held with
  | checked accepted =>
    cases instruction
    all_goals first
      | exact .checked (instruction_valid_monotone before after _ growth accepted)
      | exact .jump (.inl inside)
      | exact .zero (Nat.le_trans (by have bound := jumpIfZero_valid_bounds before _ _ accepted; omega) growth.slots) (.inl inside)
      | exact .nonzero (Nat.le_trans (by have bound := jumpIfNonZero_valid_bounds before _ _ accepted; omega) growth.slots) (.inl inside)
  | jump _ => exact .jump (.inl inside)
  | zero slot _ => exact .zero (slot.trans growth.slots) (.inl inside)
  | nonzero slot _ => exact .nonzero (slot.trans growth.slots) (.inl inside)

/-- Once the patched target names a stored instruction, the branch check is
complete; pending ownership is no longer needed for that word. -/
theorem OpenInstructionCheck.retarget_accepts {before after : runtime.bytecode.CompiledFunction}
    {pending : Nat → Prop} {index instruction}
    (held : OpenInstructionCheck before pending index instruction)
    (growth : InstructionCheckExtends before after) (target : U32)
    (inside : target.val < after.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid after (Itasca.Runtime.Code.retarget instruction target) = .ok true := by
  cases held with
  | checked accepted =>
    by_cases jump : ∃ old, instruction = .Jump old
    · obtain ⟨old,rfl⟩ := jump
      exact (CoreInstructionBounds.jump inside).accepts
    by_cases zero : ∃ condition old, instruction = .JumpIfZero condition old
    · obtain ⟨condition,old,rfl⟩ := zero
      have bound := jumpIfZero_valid_bounds before condition old accepted
      exact (CoreInstructionBounds.jumpIfZero (by have capacity := growth.slots; omega) inside).accepts
    by_cases nonzero : ∃ condition old, instruction = .JumpIfNonZero condition old
    · obtain ⟨condition,old,rfl⟩ := nonzero
      have bound := jumpIfNonZero_valid_bounds before condition old accepted
      exact (CoreInstructionBounds.jumpIfNonZero (by have capacity := growth.slots; omega) inside).accepts
    have same : Itasca.Runtime.Code.retarget instruction target = instruction := by
      cases instruction <;> simp_all [Itasca.Runtime.Code.retarget]
    rw [same]
    exact instruction_valid_monotone before after instruction growth accepted
  | jump _ => exact (CoreInstructionBounds.jump inside).accepts
  | zero slot _ => exact (CoreInstructionBounds.jumpIfZero (slot.trans growth.slots) inside).accepts
  | nonzero slot _ => exact (CoreInstructionBounds.jumpIfNonZero (slot.trans growth.slots) inside).accepts

/-- Patching removes precisely the target obligations at the listed bytecode
positions. Every unpatched pending site must retain its owner. -/
theorem OpenInstructionPrefix.patch {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (sites : List Usize) (target : U32)
    (code : after.code.val = patchCode before.code.val sites target)
    (inside : target.val ≤ after.code.length)
    (owners : ∀ index, (∀ site ∈ sites, site.val ≠ index) → pending index → next index) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code,patchCode_get] at found
  split at found
  · rename_i changed
    cases original : before.code.val[index]? with
    | none => simp [original] at found
    | some prior =>
      have same : retarget prior target = instruction := by simpa [original] using found
      rw [← same]
      exact (held index prior original).retarget growth target inside
  · rename_i unchanged
    exact (held index instruction found).grow growth (owners index (by simpa using unchanged))

end Itasca.Runtime.Code
