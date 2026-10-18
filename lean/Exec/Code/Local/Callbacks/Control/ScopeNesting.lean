import Exec.Code.Local.Callbacks.Control.ScopeFrameElse
import Exec.Code.Local.Callbacks.Control.ScopeFrameEnter
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Nested source scopes begin after their parent's body entry. The extra local
geometry also covers ELSE scopes, whose body begins at a patched destination. -/
inductive ScopeNesting : List SourceScope → SourceScope → Prop
  | root (scope : SourceScope) (geometry : scope.entry ≤ scope.bodyPc) : ScopeNesting [] scope
  | push {parents parent} (outer : ScopeNesting parents parent) (child : SourceScope)
      (order : parent.bodyPc ≤ child.entry) (geometry : child.entry ≤ child.bodyPc) :
      ScopeNesting (parents ++ [parent]) child

theorem ScopeNesting.geometry {parents current} (nested : ScopeNesting parents current) :
    current.entry ≤ current.bodyPc := by
  cases nested <;> assumption

theorem ScopeNesting.ancestor_bound {parents current} (nested : ScopeNesting parents current)
    (scope : SourceScope) (member : scope ∈ parents) : scope.bodyPc ≤ current.entry := by
  induction nested with
  | root => simp at member
  | @push parents parent outer child order geometry ih =>
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact (ih member).trans (outer.geometry.trans order)
    · exact order

theorem ScopeNesting.change_current {parents current} (nested : ScopeNesting parents current)
    (next : SourceScope) (entry : next.entry = current.entry)
    (geometry : next.entry ≤ next.bodyPc) : ScopeNesting parents next := by
  cases nested with
  | root => exact .root next geometry
  | push outer child order oldGeometry => exact .push outer next (by simpa [entry] using order) geometry

theorem ScopeNesting.advance {parents current} (nested : ScopeNesting parents current)
    (instruction : instr) : ScopeNesting parents (current.advance instruction) :=
  nested.change_current _ rfl nested.geometry

theorem ScopeNesting.begin_else {parents current} (nested : ScopeNesting parents current)
    (bt : blocktype) (condition : U32) (yesExit : Nat) (noEntry : U32) (normal : Bool)
    (order : current.entry ≤ noEntry.val) :
    ScopeNesting parents (current.begin_else bt condition yesExit noEntry normal) :=
  nested.change_current _ rfl order

theorem ScopeNesting.pop {parents parent child}
    (nested : ScopeNesting (parents ++ [parent]) child) : ScopeNesting parents parent := by
  generalize equation : parents ++ [parent] = allParents at nested
  cases nested with
  | root => simp at equation
  | @push outerParents outerParent outer current order geometry =>
    have same : parents = outerParents ∧ parent = outerParent := by simpa using equation
    rcases same with ⟨rfl, rfl⟩
    exact outer

theorem ScopeNesting.initial (returns : List valtype) : ScopeNesting [] (SourceScope.initial returns) :=
  .root _ (by simp [SourceScope.initial])

/-- A physical IF guard sits strictly before its own body. -/
theorem ScopeFrameShape.guard_geometry {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (guard : Usize)
    (found : frame.if_pc = some guard) : guard.val = scope.entry ∧ guard.val < scope.bodyPc := by
  have mapped := shape.guard
  rw [found] at mapped
  simp only [Option.map_some] at mapped
  cases form : scope.form <;> simp [SourceScope.guardPosition, form] at mapped
  rename_i bt condition
  cases entered : scope.entered <;> simp [entered] at mapped
  have body := shape.body
  simp only [SourceScope.bodyStart, form, entered, ↓reduceIte] at body
  exact ⟨mapped, by omega⟩

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

/-- Guard distinctness follows from actual frame/source alignment and scope
nesting, rather than an assumption about the compiler's chosen addresses. -/
theorem ScopeNesting.distinct_guard {locals parents current frames frame}
    (nested : ScopeNesting parents current)
    (paired : List.Forall₂ (ScopeFrameShape locals) parents frames)
    (shape : ScopeFrameShape locals current frame) (guard : Usize)
    (found : frame.if_pc = some guard) : ∀ other ∈ frames, other.if_pc ≠ some guard := by
  intro other member same
  obtain ⟨scope, present, otherShape⟩ := paired_member paired member
  have currentGuard := (shape.guard_geometry guard found).1
  have parentGuard := (otherShape.guard_geometry guard same).2
  have ordered := nested.ancestor_bound scope present
  omega
theorem ScopeNesting.enter_block {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterBlock bt front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterBlock])

theorem ScopeNesting.enter_loop {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterLoop bt front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterLoop])

theorem ScopeNesting.enter_if {A : Type} {locals parents current frame}
    {compiler : runtime.compiler.FunctionCompiler A} (nested : ScopeNesting parents current)
    (shape : FrameScope locals compiler current frame) (bt : blocktype) (condition : U32)
    (front params results : List valtype) (entered : Bool) :
    ScopeNesting (parents ++ [current])
      (SourceScope.enterIf bt condition front params results compiler.function.code.val.length entered) :=
  .push nested _ shape.bodyBound (by simp [SourceScope.enterIf])
end Exec.Code
