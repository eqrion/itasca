import Exec.Code.Local.Checking.OpenInstructionCheck
import Exec.Code.Local.Lowering.Common.Lowering

namespace Exec.Code
open Aeneas Aeneas.Std

/-- New ordinary emissions preserve every stored instruction check, including
pending branches in earlier code. Their ownership is transported explicitly. -/
theorem OpenInstructionPrefix.append {before after : runtime.bytecode.CompiledFunction}
    {pending next : Nat → Prop} (held : OpenInstructionPrefix before pending)
    (growth : InstructionCheckExtends before after) (owners : ∀ index, pending index → next index)
    (fragment : List runtime.bytecode.Instr) (code : after.code.val = before.code.val++fragment)
    (fresh : ∀ instruction ∈ fragment,
      runtime.bytecode.CompiledFunction.instruction_valid after instruction = .ok true) :
    OpenInstructionPrefix after next := by
  intro index instruction found
  rw [code] at found
  by_cases inside : index < before.code.val.length
  · rw [List.getElem?_append_left inside] at found
    exact (held index instruction found).grow growth (owners index)
  · rw [List.getElem?_append_right (by omega : before.code.val.length ≤ index)] at found
    obtain ⟨bound,equal⟩ := List.getElem?_eq_some_iff.mp found
    exact .checked (fresh instruction (equal ▸ List.getElem_mem bound))

/-- Literal lowering preserves checker capacities when its captured tables are
unchanged. This is independent of its execution simulation. -/
theorem Lowered.instructionCheckExtends {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction stack}
    (lowered : Lowered before after instruction stack)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function) :
    InstructionCheckExtends before.function after.function := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,Prod.mk.injEq] at lengths
  refine ⟨lowered.2.2.2.2,?_,?_,?_,?_,?_⟩
  · change before.function.code.val.length ≤ after.function.code.val.length
    rw [lowered.1,List.length_append,List.length_singleton]
    omega
  · change before.function.indirect.val.length ≤ after.function.indirect.val.length
    omega
  · change before.function.simd.val.length ≤ after.function.simd.val.length
    omega
  · change before.function.v128_pool.val.length ≤ after.function.v128_pool.val.length
    omega
  · change before.function.jump_tables.val.length ≤ after.function.jump_tables.val.length
    omega

/-- Unchanged captured tables and numerical code/slot growth preserve all
checker index spaces, independently of compiler control-stack mutations. -/
theorem InstructionCheckExtends.of_tables_equal (before after : runtime.bytecode.CompiledFunction)
    (tables : CompilerTables.ofFunction after = CompilerTables.ofFunction before)
    (slots : before.slot_count.val ≤ after.slot_count.val) (code : before.code.length ≤ after.code.length) :
    InstructionCheckExtends before after := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,Prod.mk.injEq] at lengths
  refine ⟨slots,code,?_,?_,?_,?_⟩
  · change before.indirect.val.length ≤ after.indirect.val.length
    omega
  · change before.simd.val.length ≤ after.simd.val.length
    omega
  · change before.v128_pool.val.length ≤ after.v128_pool.val.length
    omega
  · change before.jump_tables.val.length ≤ after.jump_tables.val.length
    omega

/-- A lowered instruction with source-derived operands extends the open check
invariant without assuming validity of the completed function. -/
theorem Lowered.openInstructionPrefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction stack} {pending next : Nat → Prop}
    (lowered : Lowered before after instruction stack)
    (tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function)
    (held : OpenInstructionPrefix before.function pending) (owners : ∀ index, pending index → next index)
    (valid : runtime.bytecode.CompiledFunction.instruction_valid after.function instruction = .ok true) :
    OpenInstructionPrefix after.function next :=
  held.append (lowered.instructionCheckExtends tables) owners [instruction] lowered.1 (by simpa using valid)

end Exec.Code
