import Exec.Code.Local.Callbacks.Control.ScopeFrameSelect
import Exec.Code.Body.Callbacks.Common.CompilerPrefix
namespace Exec.Code
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

theorem CompilerPrefix.branch_if_coordinates {A : Type}
    {initial before : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position stack}
    (invariant : CompilerPrefix initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope)
    (discarded : List valtype)
    (input : Sequence.stackTypes raw = stack ++ [.I32])
    (targetStack : stack = scope.front ++ discarded ++ scope.branchTypes) :
    ∃ index : Usize, ∃ frame : runtime.compiler.Frame, ∃ source condition : U32,
      before.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = before.frames.val.length ∧
      FrameScope locals before scope frame ∧
      frame.height.val = slots locals + slots scope.front ∧
      source.val = slots locals + slots (scope.front ++ discarded) ∧
      source.val + slots scope.branchTypes + 1 = before.height.val ∧
      before.before.val[before.before.val.length - 1]? = some condition ∧
      condition.val = slots locals + slots stack := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  obtain ⟨index, frame, found, position, shape, _, height⟩ :=
    invariant.frames.selected_live invariant.entryChain entered depth scope selected
  have layout : CompilerLayout before (stack ++ [.I32]) := input ▸ retained.layout
  obtain ⟨condition, conditionAt, conditionSlot⟩ := layout.condition
  have grouped : CompilerLayout before (scope.front ++ discarded ++ (scope.branchTypes ++ [.I32])) := by
    simpa only [targetStack, List.append_assoc] using layout
  obtain ⟨source, sourcePosition, sourceWidth⟩ := branch_source_coordinate grouped retained.localsEq
  refine ⟨index, frame, source, condition, found, position, shape, height, sourcePosition, ?_, conditionAt, ?_⟩
  · simpa [slots_append, slots, width, Nat.add_assoc] using sourceWidth
  · simpa only [retained.localsEq] using conditionSlot

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
end Exec.Code
