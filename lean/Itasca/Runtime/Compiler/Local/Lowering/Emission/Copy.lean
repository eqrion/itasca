import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit
import Itasca.Runtime.Compiler.Local.Control.Segments.Structured

/-!
The compiler's copy helper elides an empty or identity transfer.

Main declarations: `compiler_copy_elided` and `compiler_copy`. A direct consumer is `Compiler.Local.Lowering.Control.LoweringForwardBranch`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The compiler's copy helper elides an empty or identity transfer. -/
theorem compiler_copy_elided {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (dst src count : U32)
    (empty : count = 0#u32 ∨ src = dst) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count = .ok (.Ok (), compiler) := by
  rcases empty with zero | same
  · simp [runtime.compiler.FunctionCompiler.copy, zero]
  · simp [runtime.compiler.FunctionCompiler.copy, same]

/-- Every nonempty, nonidentity transfer emits the width-selected instruction. -/
@[step] theorem compiler_copy {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (dst src count : U32) (nonempty : count ≠ 0#u32) (different : src ≠ dst)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.copy ops compiler dst src count ⦃ out =>
      out.1 = .Ok () → Emitted compiler out.2 (transferInstruction dst src count) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.copy
  rw [if_neg nonempty, if_neg different]
  split
  · simp only [bind_ok]
    simpa [transferInstruction, UScalar.val] using
      compiler_emit ops law compiler (.Copy dst src) codeFits sourceFits coordinateFits
  · simp only [bind_ok]
    simpa [transferInstruction, UScalar.val] using
      compiler_emit ops law compiler (.Copy2 dst src) codeFits sourceFits coordinateFits
  · rename_i notOne notTwo
    simp only [bind_ok]
    have h1 : count.val ≠ 1 := by
      intro eq
      apply notOne
      apply UScalar.eq_of_val_eq
      exact eq
    have h2 : count.val ≠ 2 := by
      intro eq
      apply notTwo
      apply UScalar.eq_of_val_eq
      exact eq
    simpa [transferInstruction, h1, h2] using
      compiler_emit ops law compiler (.CopyN dst src count) codeFits sourceFits coordinateFits
end Itasca.Runtime.Compiler
