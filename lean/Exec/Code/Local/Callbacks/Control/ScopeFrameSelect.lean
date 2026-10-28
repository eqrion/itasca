import Exec.Code.Local.Source.SourceEntryChain
import Exec.Code.Local.Relations.Common.CompileInv
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

private theorem paired_lookup {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (item : α)
    (found : left[index]? = some item) : ∃ value, right[index]? = some value ∧ R item value := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst item; exact ⟨b, rfl, head⟩
    | succ index => exact ih index found

private theorem paired_reverse {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) : List.Forall₂ R left.reverse right.reverse := by
  induction paired with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using List.rel_append ih (.cons head .nil)

/-- Reverse source depth selects the same retained physical frame. -/
theorem ScopeFrameStack.selected {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals compiler parents current)
    (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ index : Usize, ∃ frame,
      compiler.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = compiler.frames.val.length ∧
      FrameScope locals compiler scope frame := by
  have paired : List.Forall₂ (FrameScope locals compiler)
      (current :: parents.reverse) compiler.frames.val.reverse := by
    simpa only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append] using paired_reverse stack.frames
  obtain ⟨frame, reversed, shape⟩ := paired_lookup paired depth scope selected
  have bound := (List.getElem?_eq_some_iff.mp reversed).1
  simp only [List.length_reverse] at bound
  let index : Usize := UScalar.ofNatCore (compiler.frames.val.length - 1 - depth) (by
    have size : compiler.frames.val.length ≤ Usize.max := by scalar_tac
    scalar_tac)
  refine ⟨index, frame, ?_, ?_, shape⟩
  · change compiler.frames.val[compiler.frames.val.length - 1 - depth]? = some frame
    simpa only [List.getElem?_reverse bound] using reversed
  · change compiler.frames.val.length - 1 - depth + depth + 1 = compiler.frames.val.length
    omega

/-- Live scopes obtain source slot geometry from the retained frame, including
ancestor scopes selected by a nonzero branch depth. -/
theorem ScopeFrameStack.selected_live {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals compiler parents current)
    (chain : SourceEntryChain parents current) (live : current.entered = true)
    (depth : Nat) (scope : SourceScope)
    (selected : (current :: parents.reverse)[depth]? = some scope) :
    ∃ index : Usize, ∃ frame,
      compiler.frames.val[index.val]? = some frame ∧
      index.val + depth + 1 = compiler.frames.val.length ∧
      FrameScope locals compiler scope frame ∧
      scope.entered = true ∧ frame.height.val = slots locals + slots scope.front := by
  obtain ⟨index, frame, found, position, shape⟩ := stack.selected depth scope selected
  have member : scope ∈ parents ++ [current] := by
    have member := List.mem_of_getElem? selected
    simpa only [List.mem_cons, List.mem_reverse, List.mem_append, List.mem_singleton, List.mem_nil_iff, or_false, false_or, or_comm] using member
  have entered := chain.all_entered live scope member
  exact ⟨index, frame, found, position, shape, entered, shape.height entered⟩


theorem ScopeFrameShape.branch_width {locals scope} {frame : runtime.compiler.Frame}
    (shape : ScopeFrameShape locals scope frame) :
    (match frame.kind with | .Loop => frame.params | _ => frame.results).val = slots scope.branchTypes := by
  rw [shape.kind]
  cases form : scope.form <;> simp [ScopeForm.kind, SourceScope.branchTypes, form, shape.params, shape.results]

/-- The source coordinate used by an actual branch is representable because it
is a prefix of the current checked live operand-stack layout. -/
theorem branch_source_coordinate {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {locals target discarded arguments : List valtype}
    (layout : CompilerLayout compiler (target ++ discarded ++ arguments))
    (localTypes : compilerLocals compiler = locals) :
    ∃ source : U32, source.val = slots locals + slots (target ++ discarded) ∧
      source.val + slots arguments = compiler.height.val := by
  have height : compiler.height.val = slots locals + slots (target ++ discarded ++ arguments) := by
    simpa only [localTypes] using layout.height
  have bound := compiler.height.hBounds
  change compiler.height.val < 2^32 at bound
  have sum : slots (target ++ discarded ++ arguments) = slots (target ++ discarded) + slots arguments := slots_append _ _
  let source : U32 := UScalar.ofNatCore (slots locals + slots (target ++ discarded)) (by change slots locals + slots (target ++ discarded) < 2^32; omega)
  refine ⟨source, rfl, ?_⟩
  change slots locals + slots (target ++ discarded) + slots arguments = compiler.height.val
  omega
end Itasca.Runtime.Code
