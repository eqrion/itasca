import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

theorem CompilerLayout.condition {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {stack : List valtype} (layout : CompilerLayout compiler (stack ++ [.I32])) :
    ∃ condition : U32,
      compiler.before.val[compiler.before.val.length - 1]? = some condition ∧
      condition.val = slots (compilerLocals compiler) + slots stack := by
  have length := layout.operands_length
  simp only [List.length_append, List.length_singleton] at length
  have bound : stack.length < compiler.before.val.length := by omega
  let condition := compiler.before.val[stack.length]'bound
  have atIndex : compiler.before.val[stack.length]? = some condition := List.getElem?_eq_getElem bound
  refine ⟨condition, ?_, ?_⟩
  · have index : compiler.before.val.length - 1 = stack.length := by omega
    simpa only [index] using atIndex
  · have mapped := congrArg (fun list => list[stack.length]?) layout.operandOffsets
    simpa [stackOffsets, List.getElem?_map, atIndex, offset] using mapped

theorem SourceCodeBudget.branch_resume {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (count source destination : U32) :
    ∃ resume : U32, resume.val = compiler.function.code.val.length +
      (if count = 0#u32 ∨ source = destination then 1 else 3) := by
  have fits : compiler.function.code.val.length + 3 < 2^32 := by
    unfold SourceCodeBudget at budget
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    omega
  let pc := compiler.function.code.val.length + (if count = 0#u32 ∨ source = destination then 1 else 3)
  have bound : pc < 2^32 := by dsimp [pc]; split <;> omega
  exact ⟨UScalar.ofNatCore pc bound, rfl⟩
end Itasca.Runtime.Code
