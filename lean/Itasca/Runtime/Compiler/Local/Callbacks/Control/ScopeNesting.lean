import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFramePatch
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameElse

/-!
Source-scope entry forms and their nesting geometry. ScopeNesting gives ancestor bounds needed by control-map and frame-stack proofs.
-/

/-! ## Scope Frame Enter -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def SourceScope.enterBlock (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.block bt, front, params, results, [], entry, entry, entered⟩

def SourceScope.enterLoop (bt : blocktype) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.loop bt, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

def SourceScope.enterIf (bt : blocktype) (condition : U32) (front params results : List valtype)
    (entry : Nat) (entered : Bool) : SourceScope :=
  ⟨.then_ bt condition, front, params, results, [], entry, entry + (if entered then 1 else 0), entered⟩

/-- The exact freshly pushed BLOCK frame matches its new source scope. -/
theorem FrameScope.enter_block {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val ≤ compiler.function.code.val.length) :
    FrameScope locals compiler (SourceScope.enterBlock bt front params results pc.val entered)
      ⟨map, .Block, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterBlock, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · exact position
  · exact position
  · trivial

/-- A freshly pushed LOOP retains its hook only when source entry was live. -/
theorem FrameScope.enter_loop {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (map : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (position : pc.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length)
    (hook : entered = true → compiler.function.code.val[pc.val]? = some .LoopHead) :
    FrameScope locals compiler (SourceScope.enterLoop bt front params results pc.val entered)
      ⟨map, .Loop, height, paramWidth, resultWidth, pc, none, entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterLoop, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition, alloc.vec.Vec.new]
  · exact mapBound
  · change pc.val ≤ compiler.function.code.val.length
    omega
  · exact position
  · exact hook

/-- An entered IF owns a fresh guard immediately before its frame's start PC. -/
theorem FrameScope.enter_if {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (locals front params results : List valtype) (bt : blocktype) (condition : U32) (map entry : Usize)
    (height paramWidth resultWidth pc : U32) (entered : Bool)
    (paramsEq : paramWidth.val = slots params) (resultsEq : resultWidth.val = slots results)
    (heightEq : entered = true → height.val = slots locals + slots front)
    (mapBound : map.val < compiler.function.controls.val.length)
    (start : pc.val = entry.val + (if entered then 1 else 0))
    (position : pc.val ≤ compiler.function.code.val.length)
    (guard : entered = true → compiler.function.code.val[entry.val]? = some (.JumpIfZero condition core.num.U32.MAX)) :
    FrameScope locals compiler (SourceScope.enterIf bt condition front params results entry.val entered)
      ⟨map, .Then, height, paramWidth, resultWidth, pc, (if entered then some entry else none),
        entered, false, alloc.vec.Vec.new Usize⟩ := by
  constructor
  · constructor <;> simp_all [SourceScope.enterIf, ScopeForm.kind, SourceScope.frameStart,
      SourceScope.bodyStart, SourceScope.guardPosition]
  · exact mapBound
  · change entry.val ≤ compiler.function.code.val.length
    omega
  · change entry.val + (if entered then 1 else 0) ≤ compiler.function.code.val.length
    omega
  · exact guard
end Itasca.Runtime.Compiler

end

/-! ## Scope Nesting -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
