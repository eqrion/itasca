import Exec.Code.Local.Callbacks.Control.ScopeFrameStack
import Exec.Code.Local.Callbacks.Control.ScopeFrameGuardAppend
import Exec.Code.Local.Callbacks.Control.ElseTransition
namespace Exec.Code
open Aeneas Aeneas.Std

theorem ScopeFrameStack.parts {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame]) :
    List.Forall₂ (FrameScope locals compiler) parents prior ∧ FrameScope locals compiler current frame := by
  obtain ⟨actualPrior, actualFrame, actualFrames, paired, shape⟩ := stack.split
  have equal : actualPrior = prior ∧ actualFrame = frame := by
    simpa using actualFrames.symm.trans frames
  rcases equal with ⟨rfl, rfl⟩
  exact ⟨paired, shape⟩

theorem scopeFrames_imp_member {α β : Type} {R S : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right)
    (change : ∀ a b, b ∈ right → R a b → S a b) : List.Forall₂ S left right := by
  induction paired with
  | nil => exact .nil
  | @cons a b left right related rest ih =>
    exact .cons (change a b (by simp) related)
      (ih (fun a b member related => change a b (List.mem_cons_of_mem _ member) related))

/-- The exact ELSE mutation preserves every paired frame, deriving outer guard
distinctness from nesting and updating the active scope's second-arm geometry. -/
theorem ScopeFrameStack.begin_else {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (guard site : Usize) (condition old noEntry : U32) (fixups : alloc.vec.Vec Usize) (normal : Bool)
    (change : ElseTransition before after prior frame guard site condition old noEntry fixups normal)
    (bt : blocktype) (form : current.form = .then_ bt condition) (guardEq : frame.if_pc = some guard)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents
      (current.begin_else bt condition before.function.code.val.length noEntry normal) := by
  obtain ⟨paired, shape⟩ := stack.parts prior frame change.beforeFrames
  have distinct := stack.distinct_guard prior frame change.beforeFrames guard guardEq
  have retained : List.Forall₂ (FrameScope locals after) parents prior := by
    apply scopeFrames_imp_member paired
    intro scope other member original
    exact original.set_guard_append _ guard condition old noEntry change.guardCode
      (distinct other member) change.codeEq maps
  have fresh := shape.begin_else bt condition form before.function.code.val.length noEntry normal fixups
    maps change.order (Nat.le_of_eq change.length.symm)
  apply stack.replace_current _ prior _ change.afterFrames retained fresh rfl
  change current.entry ≤ noEntry.val
  have bounded := shape.entryBound
  rw [change.noPosition]
  omega
end Exec.Code
