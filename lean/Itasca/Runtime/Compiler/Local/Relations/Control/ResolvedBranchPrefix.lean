import Itasca.Runtime.Compiler.Local.Relations.Control.ControlLayout
import Itasca.Runtime.Compiler.Local.Initializer.InitializerElementAppend
import Itasca.Runtime.Compiler.Local.Relations.Emission.EmissionSources
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Copy
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix

/-!
Sections, each formerly its own module: BranchSuccessEmit, ResolvedBranchPrefix.
-/

/-! ## BranchSuccessEmit -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
/-- Exact successful emission needs no separate vector-capacity or coordinate premise. -/
theorem compiler_emit_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (instruction : runtime.bytecode.Instr)
    (accepted : runtime.compiler.FunctionCompiler.emit ops before instruction = .ok (.Ok (), after)) :
    Emitted before after instruction := by
  exact (((runtime.compiler.FunctionCompiler.emit.inv ops before after instruction (.Ok ()) accepted).2 law).2 rfl).emitted

theorem compiler_copy_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (nonempty : count ≠ 0#u32) (different : src ≠ dst)
    (accepted : runtime.compiler.FunctionCompiler.copy ops before dst src count = .ok (.Ok (), after)) :
    Emitted before after (transferInstruction dst src count) := by
  unfold runtime.compiler.FunctionCompiler.copy at accepted
  rw [if_neg nonempty, if_neg different] at accepted
  split at accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy dst src) accepted
  · simp only [bind_ok] at accepted
    simpa [transferInstruction, UScalar.val] using compiler_emit_success ops law before after (.Copy2 dst src) accepted
  · rename_i notOne notTwo
    simp only [bind_ok] at accepted
    have h1 : count.val ≠ 1 := by intro eq; apply notOne; apply UScalar.eq_of_val_eq; exact eq
    have h2 : count.val ≠ 2 := by intro eq; apply notTwo; apply UScalar.eq_of_val_eq; exact eq
    simpa [transferInstruction, h1, h2] using compiler_emit_success ops law before after (.CopyN dst src count) accepted
end Itasca.Runtime.Compiler

end

/-! ## ResolvedBranchPrefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Retargeting a newly emitted BR in its selected open group preserves the
previous resolved prefix and appends the final literal branch sequence. -/
theorem resolved_code_new_br (code : List Bytecode) (before after : List FixupTarget)
    (group : FixupTarget) (dst src count old : U32) (site : Usize)
    (position : site.val = code.length + (if count = 0#u32 ∨ src = dst then 0 else 1))
    (inside : FixupsInside (before ++ group :: after) code.length) :
    resolvedCode (code ++ branchInstructions dst src count old)
      (before ++ {group with sites := group.sites ++ [site]} :: after) =
      resolvedCode code (before ++ group :: after) ++ branchInstructions dst src count group.target := by
  by_cases elided : count = 0#u32 ∨ src = dst
  · simpa [branchInstructions, elided, BranchKind.instruction] using
      resolved_code_new_branch code [] before after group .jump old site (by simpa [elided] using position) inside
  · simpa [branchInstructions, elided, BranchKind.instruction, List.append_assoc] using
      resolved_code_new_branch code [transferInstruction dst src count] before after group .jump old site
        (by simpa [elided] using position) inside

end Itasca.Runtime.Compiler

end
