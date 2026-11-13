import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission
import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormedAcceptance
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdInstructionAcceptance
import Itasca.Runtime.Compiler.Local.Checking.ScopeEntryInstructionPrefix

/-!
Sections, each formerly its own module: ExecutableInstructionAcceptance, ExecutableInstructionPrefix.
-/

/-! ## ExecutableInstructionAcceptance -/

section

/-!
Explicit select has the same width-specific checker as ordinary select.

Main declarations: `TypedSelectEmission.instructions_accept` and `ExecutableEmission.ordinary_instructions_accept`. A direct consumer is `Compiler.Body.Relations.Checking.ExecutableInstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Explicit select has the same width-specific checker as ordinary select. -/
theorem TypedSelectEmission.instructions_accept {C before source emitted after}
    (emission : TypedSelectEmission C before source emitted after)
    (function : runtime.bytecode.CompiledFunction)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | select front ty left right condition first second test =>
    exact (ScalarEmission.select front ty left right condition first second test).instructions_accept function inputs outputs

/-- Every ordinary complete-profile emission passes the bytecode checker from
source stack capacities and the exact retained tables. Branch-table gates are
checked separately with their structural target-table layout. -/
theorem ExecutableEmission.ordinary_instructions_accept (function : runtime.bytecode.CompiledFunction)
    {C before source emitted after}
    (emission : ExecutableEmission (CompilerTables.ofFunction function) C before source emitted after)
    (ordinary : ∀ depths fallback, source ≠ .BR_TABLE depths fallback)
    (inputs : slots C.LOCALS+slots before ≤ function.slot_count.val)
    (outputs : slots C.LOCALS+slots after ≤ function.slot_count.val) :
    ∀ instruction ∈ emitted,
      runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  cases emission with
  | scalar head => exact head.instructions_accept function inputs outputs
  | stateful head => exact head.instructions_accept function rfl inputs outputs
  | indirect head => exact head.instructions_accept function rfl inputs
  | simd head => exact head.instructions_accept function rfl rfl inputs outputs
  | typedSelect head => exact head.instructions_accept function inputs outputs
  | branchTable stack depths fallback selector start len => exact False.elim (ordinary depths fallback rfl)

end Itasca.Runtime.Compiler

end

/-! ## ExecutableInstructionPrefix -/

section

/-!
Captured table appends increase every local checker index space. The contents are separately related to source syntax by emission certificates.

Main declarations: `instruction_check_extends_of_tables_append` and `Lowered.executable_instruction_prefix`. A direct consumer is `Compiler.Body.Reader.Calls.InstructionPrefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Captured table appends increase every local checker index space. The
contents are separately related to source syntax by emission certificates. -/
theorem instruction_check_extends_of_tables_append (before after : runtime.bytecode.CompiledFunction)
    (extra : CompilerTables)
    (tables : CompilerTables.ofFunction after = (CompilerTables.ofFunction before).append extra)
    (slots : before.slot_count.val ≤ after.slot_count.val) (code : before.code.length ≤ after.code.length) :
    InstructionCheckExtends before after := by
  have lengths := congrArg (fun tables => (tables.indirect.length,tables.simd.length,tables.constants.length,tables.jumpTables.length)) tables
  simp only [CompilerTables.ofFunction,CompilerTables.append,List.length_append,Prod.mk.injEq] at lengths
  refine ⟨slots,code,?_,?_,?_,?_⟩
  · change before.indirect.val.length ≤ after.indirect.val.length
    omega
  · change before.simd.val.length ≤ after.simd.val.length
    omega
  · change before.v128_pool.val.length ≤ after.v128_pool.val.length
    omega
  · change before.jump_tables.val.length ≤ after.jump_tables.val.length
    omega

/-- All ordinary complete-profile source emissions preserve checking of every
stored instruction, including outstanding branches in older code. Appended
SIMD, constant, and indirect-call metadata are allowed. -/
theorem Lowered.executable_instruction_prefix {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {instruction input output source C}
    (lowered : Lowered before after instruction output) (layout : CompilerLayout before input)
    (live : before.reachable = true) (locals : C.LOCALS = compilerLocals before)
    (emission : ExecutableEmission (CompilerTables.ofFunction after.function) C input source [instruction] output)
    (ordinary : ∀ depths fallback, source ≠ .BR_TABLE depths fallback)
    (growth : InstructionCheckExtends before.function after.function)
    (held : CompilerInstructionPrefix before) (frames : after.frames = before.frames) :
    CompilerInstructionPrefix after := by
  obtain ⟨inputs,outputs⟩ := lowered.source_capacities layout live
  have valid := emission.ordinary_instructions_accept after.function ordinary
    (by simpa only [locals] using inputs) (by simpa only [locals] using outputs)
  refine held.append growth ?_ [instruction] lowered.1 (by simpa using valid instruction (by simp))
  intro index owned
  simpa only [PendingInstructionSite,frames] using owned

end Itasca.Runtime.Compiler

end
