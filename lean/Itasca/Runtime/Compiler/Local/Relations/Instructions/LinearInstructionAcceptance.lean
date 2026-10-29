import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericInstructionPublication
import Itasca.Runtime.Compiler.Local.Relations.Instructions.CoreInstructionAcceptance

/-!
A typed local transfer fits whether the value occupies one word or two.

Main declarations: `move_instruction_accepts` and `LinearEmission.instructions_accept`. A direct consumer is `Compiler.Local.Relations.Instructions.ScalarEmissionAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A typed local transfer fits whether the value occupies one word or two. -/
theorem move_instruction_accepts (function : runtime.bytecode.CompiledFunction) (ty : valtype) (dst src : U32)
    (destination : dst.val+width ty ≤ function.slot_count.val)
    (source : src.val+width ty ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.instruction_valid function (move ty dst src) = .ok true := by
  have widths : width ty = 1 ∨ width ty = 2 := by cases ty <;> decide
  rcases widths with one | two
  · simp only [move,one,Nat.reduceEqDiff,↓reduceIte]
    exact (CoreInstructionBounds.copy (by omega) (by omega)).accepts
  · simp only [move,two,↓reduceIte]
    exact (CoreInstructionBounds.copy2 (by omega) (by omega)).accepts

/-- Source-indexed literal emissions pass the actual bytecode checker when
both source stack boundaries fit. This checks every emitted bytecode word,
independently of any semantic reachability in the completed function. -/
theorem LinearEmission.instructions_accept {locals before source emitted after}
    (emission : LinearEmission locals before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots locals+slots before ≤ function.slot_count.val)
    (outputs : slots locals+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | nop | drop => simp
  | const32 stack dst word position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const32 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | const64 stack dst word position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    apply CoreInstructionBounds.accepts (.const64 _)
    simp only [slots_append,slots,width] at outputs
    omega
  | binary stack ty op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : right.val+1 ≤ function.slot_count.val := by
      cases ty <;> simp [integerType,slots_append,slots,width] at inputs <;> omega
    have firstBound : left.val+1 ≤ function.slot_count.val := by omega
    cases ty <;> cases op
    all_goals apply scalar_instruction_accepts function _ _ _ _ _ rfl firstBound firstBound bound
  | numeric stack op left right first second =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    exact numeric_instruction_accepts function locals stack op left right first second inputs
  | eqz32 stack operand position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : operand.val+1 ≤ function.slot_count.val := by
      simp only [slots_append,slots,width] at inputs
      omega
    exact scalar_instruction_accepts function _ 69#u16 operand operand operand rfl bound bound bound
  | eqz64 stack operand position =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have bound : operand.val+1 ≤ function.slot_count.val := by
      simp only [slots_append,slots,width] at inputs
      omega
    exact scalar_instruction_accepts function _ 80#u16 operand operand operand rfl bound bound bound
  | localGet stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at outputs
    apply move_instruction_accepts function ty stackSlot localSlot <;> omega
  | localSet stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at inputs
    apply move_instruction_accepts function ty localSlot stackSlot <;> omega
  | localTee stack ty index localSlot stackSlot localType localPos stackPos =>
    intro instruction member
    simp only [List.mem_singleton] at member
    subst instruction
    have localBound := offset_add_width_le localType
    simp only [slots_append,slots] at inputs
    apply move_instruction_accepts function ty localSlot stackSlot <;> omega

end Itasca.Runtime.Compiler
