import Exec.Code.Local.Lowering.Common.Lowering
/-! Actual integer-add callbacks preserve the source-prefix lowering relation.
Operand addresses come from the compiler's live layout; the proof then follows
the extracted opcode classifier, constructor, emitter, and post-stack observer. -/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

theorem binary_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front : List valtype) (ty : Inn)
    (layout : CompilerLayout compiler (front ++ [integerType ty, integerType ty])) :
    ∃ left right : U32,
      runtime.compiler.FunctionCompiler.operand ops compiler 2#usize = .ok (.Ok left) ∧
      runtime.compiler.FunctionCompiler.operand ops compiler 1#usize = .ok (.Ok right) ∧
      left.val = slots (compilerLocals compiler) + slots front ∧ right.val = left.val + 1 := by
  obtain ⟨r, hr, left, rfl, hl⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 2#usize (by decide) (by simp))
  obtain ⟨r, hr', right, rfl, hh⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout 1#usize (by decide) (by simp))
  have leftPos : left.val = slots (compilerLocals compiler) + slots front := by
    simpa [offset, List.take_append] using hl
  have rightPos : right.val = left.val + 1 := by
    have take : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
    rw [leftPos]
    cases ty <;> simpa [offset, List.take_append, slots_append, slots, width, integerType, take,
      Nat.add_assoc] using hh
  exact ⟨left, right, hr, hr', leftPos, rightPos⟩

end Itasca.Runtime.Code
