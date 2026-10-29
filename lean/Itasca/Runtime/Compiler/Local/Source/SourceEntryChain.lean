import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameStack
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- An entered child has entered ancestors. Unreachable child scopes impose
no liveness obligation on the parent that syntactically contains them. -/
inductive SourceEntryChain : List SourceScope → SourceScope → Prop
  | root (current : SourceScope) (entered : current.entered = true) : SourceEntryChain [] current
  | push {parents parent} (outer : SourceEntryChain parents parent) (child : SourceScope)
      (entered : child.entered = true → parent.entered = true) :
      SourceEntryChain (parents ++ [parent]) child

theorem SourceEntryChain.change_current {parents current} (chain : SourceEntryChain parents current)
    (next : SourceScope) (entered : next.entered = current.entered) : SourceEntryChain parents next := by
  cases chain with
  | root _ live => exact .root next (entered.trans live)
  | push outer child live => exact .push outer next (by simpa [entered] using live)

/-- The function root was entered even if its current path has terminated. -/
theorem SourceEntryChain.root_entered {parents current} (chain : SourceEntryChain parents current)
    (root : parents = []) : current.entered = true := by
  cases chain with
  | root _ live => exact live
  | push outer child entered => simp at root

theorem SourceEntryChain.advance {parents current} (chain : SourceEntryChain parents current)
    (instruction : instr) : SourceEntryChain parents (current.advance instruction) :=
  chain.change_current _ rfl

theorem SourceEntryChain.begin_else {parents current} (chain : SourceEntryChain parents current)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool) :
    SourceEntryChain parents (current.begin_else bt condition yesExit noEntry normal) :=
  chain.change_current _ rfl

theorem SourceEntryChain.pop {parents parent current}
    (chain : SourceEntryChain (parents ++ [parent]) current) : SourceEntryChain parents parent := by
  generalize equation : parents ++ [parent] = allParents at chain
  cases chain with
  | root => simp at equation
  | @push outerParents outerParent outer child entered =>
    have same : parents = outerParents ∧ parent = outerParent := by simpa using equation
    rcases same with ⟨rfl, rfl⟩
    exact outer

theorem SourceEntryChain.ancestor {parents current} (chain : SourceEntryChain parents current)
    (live : current.entered = true) (scope : SourceScope) (member : scope ∈ parents) : scope.entered = true := by
  induction chain with
  | root => simp at member
  | @push parents parent outer child entered ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact ih (entered live) member
    · exact entered live

theorem SourceEntryChain.all_entered {parents current} (chain : SourceEntryChain parents current)
    (live : current.entered = true) (scope : SourceScope) (member : scope ∈ parents ++ [current]) : scope.entered = true := by
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact chain.ancestor live scope member
  · exact live

private theorem paired_member {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) {value : β} (member : value ∈ right) :
    ∃ item, item ∈ left ∧ R item value := by
  induction paired with
  | nil => simp at member
  | @cons a b left right related rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨a, by simp, related⟩
    · obtain ⟨item, present, related⟩ := ih member
      exact ⟨item, List.mem_cons_of_mem _ present, related⟩

/-- A live branch selects an entered physical frame at every valid depth. -/
theorem ScopeFrameStack.frame_entered {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (chain : SourceEntryChain parents current) (live : current.entered = true)
    (frame : runtime.compiler.Frame) (member : frame ∈ compiler.frames.val) : frame.entry_reachable = true := by
  obtain ⟨scope, present, shape⟩ := paired_member stack.frames member
  exact shape.entered.trans (chain.all_entered live scope present)
end Itasca.Runtime.Compiler
