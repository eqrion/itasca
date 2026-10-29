import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowering
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission

/-!
Actual compiler operand reads and coordinates follow from the source signature and full stack layout, including reference values.

Main declarations: `stateful_operands`. A direct consumer is `Compiler.Local.Relations.Stateful.StatefulLowered`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem first_suffix_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front input : List valtype)
    (layout : CompilerLayout compiler (front ++ input)) (depth : Usize)
    (positive : 0 < depth.val) (count : depth.val = input.length) :
    ∃ first : U32, runtime.compiler.FunctionCompiler.operand ops compiler depth = .ok (.Ok first) ∧
      first.val = slots (compilerLocals compiler) + slots front := by
  obtain ⟨r,read,first,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout depth positive (by simp [count]))
  refine ⟨first,read,?_⟩
  simpa [offset,List.length_append,count] using position

private theorem next_suffix_operand {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (front input : List valtype)
    (layout : CompilerLayout compiler (front ++ input)) (depth : Usize)
    (positive : 0 < depth.val) (count : depth.val + 1 = input.length)
    (scalar : ∀ type ∈ input, type ≠ valtype.V128) :
    ∃ second : U32, runtime.compiler.FunctionCompiler.operand ops compiler depth = .ok (.Ok second) ∧
      second.val = slots (compilerLocals compiler) + slots front + 1 := by
  obtain ⟨r,read,second,rfl,position⟩ := WP.spec_imp_exists
    (compiler_operand ops compiler _ layout depth positive (by simp only [List.length_append]; omega))
  have index : (front ++ input).length - depth.val = front.length + 1 := by
    simp only [List.length_append]; omega
  have takeFront : front.take (front.length + 1) = front := List.take_of_length_le (by omega)
  have firstWidth : slots (input.take 1) = 1 := by
    cases input with
    | nil => simp at count
    | cons head tail =>
      have nonvector := scalar head (by simp)
      cases head <;> simp_all [slots,width]
  refine ⟨second,read,?_⟩
  rw [index] at position
  simpa [offset,List.take_append,takeFront,slots_append,firstWidth,Nat.add_assoc] using position

/-- Actual compiler operand reads and coordinates follow from the source
signature and full stack layout, including reference values. -/
theorem stateful_operands {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (C : context)
    (front input output : List valtype) (op : SourceMachine.Stateful.Instruction)
    (signature : SourceMachine.Stateful.Signature C op input output)
    (layout : CompilerLayout compiler (front ++ input)) :
    ∃ first second : U32, StatefulReads ops compiler op first second ∧
      first.val = slots (compilerLocals compiler) + slots front ∧
      (op.arity ≥ 2 → second.val = first.val + 1) := by
  have count := signature.input_length
  have bound := op.arity_le_three
  have alternatives : op.arity = 0 ∨ op.arity = 1 ∨ op.arity = 2 ∨ op.arity = 3 := by omega
  rcases alternatives with zero | one | two | three
  · have empty : input = [] := List.length_eq_zero_iff.mp (count.trans zero)
    refine ⟨compiler.height,compiler.height,⟨?_,?_⟩,?_,?_⟩
    · simp [StatefulReads,zero]
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · simpa [empty] using layout.height
    · omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 1#usize (by decide) (by simpa [one] using count.symm)
    refine ⟨first,first,⟨?_,?_⟩,position,?_⟩
    · simpa [one,statefulDepth] using read
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 2#usize (by decide) (by simpa [two] using count.symm)
    obtain ⟨second,readSecond,secondPosition⟩ := next_suffix_operand ops compiler front input layout 1#usize (by decide)
      (by simpa [two] using count.symm) signature.inputs_scalar
    refine ⟨first,second,⟨?_,?_⟩,position,?_⟩
    · simpa [two,statefulDepth] using read
    · intro table same; exact readSecond
    · intro _; omega
  · obtain ⟨first,read,position⟩ := first_suffix_operand ops compiler front input layout 3#usize (by decide) (by simpa [three] using count.symm)
    obtain ⟨second,readSecond,secondPosition⟩ := next_suffix_operand ops compiler front input layout 2#usize (by decide)
      (by simpa [three] using count.symm) signature.inputs_scalar
    refine ⟨first,second,⟨?_,?_⟩,position,?_⟩
    · simpa [three,statefulDepth] using read
    · intro table same
      have impossible := congrArg SourceMachine.Stateful.Instruction.arity same
      change op.arity = 2 at impossible
      omega
    · intro _; omega

end Itasca.Runtime.Compiler
