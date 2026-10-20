import Exec.Code.Local.Relations.Common.InstructionCheckMonotone
import Exec.Code.Local.Callbacks.Table.CompilerTablePreservation
import Exec.Code.Local.Callbacks.Common.CompilerMetadata

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Every instruction in this concrete code vector passes its local checker.
Open control fixups require a separate pending-branch invariant. -/
def CheckedInstructionPrefix (function : runtime.bytecode.CompiledFunction) : Prop :=
  ∀ instruction ∈ function.code.val,
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true

theorem CheckedInstructionPrefix.indexed {function : runtime.bytecode.CompiledFunction}
    (held : CheckedInstructionPrefix function) (index : Nat) (bound : index < function.code.length) :
    runtime.bytecode.CompiledFunction.instruction_valid function function.code.val[index] = .ok true :=
  held _ (List.getElem_mem bound)

theorem InstructionCheckExtends.refl (function : runtime.bytecode.CompiledFunction) :
    InstructionCheckExtends function function := ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩

theorem InstructionCheckExtends.trans {first middle last : runtime.bytecode.CompiledFunction}
    (left : InstructionCheckExtends first middle) (right : InstructionCheckExtends middle last) :
    InstructionCheckExtends first last :=
  ⟨left.slots.trans right.slots,left.code.trans right.code,left.indirect.trans right.indirect,
    left.simd.trans right.simd,left.constants.trans right.constants,left.targets.trans right.targets⟩

/-- Appending code retains earlier instruction checks under numerical growth
and checking of the new fragment in the resulting function. -/
theorem CheckedInstructionPrefix.append {before after : runtime.bytecode.CompiledFunction}
    (held : CheckedInstructionPrefix before) (growth : InstructionCheckExtends before after)
    (fragment : List runtime.bytecode.Instr) (code : after.code.val = before.code.val++fragment)
    (valid : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true) :
    CheckedInstructionPrefix after := by
  intro instruction member
  rw [code] at member
  rcases List.mem_append.mp member with old | fresh
  · exact instruction_valid_monotone before after instruction growth (held instruction old)
  · exact valid instruction fresh

/-- Actual emission extends all checker capacities, without changing tables. -/
theorem Emitted.instructionCheckExtends {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction) :
    InstructionCheckExtends before.function after.function := by
  obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
  refine ⟨le_rfl,?_,le_rfl,le_rfl,le_rfl,le_rfl⟩
  change before.function.code.val.length ≤ code.val.length
  rw [appended,List.length_append,List.length_singleton]
  omega

/-- A newly checked emission preserves the checked prefix. -/
theorem Emitted.checkedInstructionPrefix {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {instruction : runtime.bytecode.Instr} (emitted : Emitted before after instruction)
    (held : CheckedInstructionPrefix before.function)
    (valid : runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    CheckedInstructionPrefix after.function := by
  have appended : after.function.code.val = before.function.code.val++[instruction] := by
    obtain ⟨budget,code,sources,rfl,appended,_⟩ := emitted
    exact appended
  exact held.append emitted.instructionCheckExtends [instruction] appended (by simpa using valid)

/-- Successful observation changes only slot capacity, so every instruction
that checked before observation still checks afterwards. -/
theorem compiler_observe_checked_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (held : CheckedInstructionPrefix before.function)
    (called : runtime.compiler.FunctionCompiler.observe ops before state = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function := by
  have stable := compiler_observe_stable ops law before after state called
  have frame := compiler_observe_frame ops law before state
  rw [called,WP.spec_ok] at frame
  dsimp only at frame
  have growth : InstructionCheckExtends before.function after.function := by
    refine ⟨stable.capacity,?_,?_,?_,?_,?_⟩ <;> rw [frame] <;> exact le_rfl
  have same : after.function.code.val = before.function.code.val := by rw [frame]
  exact held.append growth [] (by simpa using same) (by simp)

end Exec.Code
