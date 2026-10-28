import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeNesting
import Itasca.Runtime.Code.Local.Callbacks.Control.ScopeFrameGuard
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Every physical frame is paired with its exact source scope, ordered from
outermost to innermost, with source-entry geometry retained across suspension. -/
structure ScopeFrameStack {A : Type} (locals : List valtype)
    (compiler : runtime.compiler.FunctionCompiler A) (parents : List SourceScope)
    (current : SourceScope) : Prop where
  nested : ScopeNesting parents current
  frames : List.Forall₂ (FrameScope locals compiler) (parents ++ [current]) compiler.frames.val

private theorem paired_last {α β : Type} {R : α → β → Prop} {left right value}
    (same : List.Forall₂ R left (right ++ [value])) :
    ∃ beginning item, left = beginning ++ [item] ∧ List.Forall₂ R beginning right ∧ R item value := by
  have beginning := List.forall₂_take_append left right [value] same
  have ending := List.forall₂_drop_append left right [value] same
  have singleton : ∀ {items : List α}, List.Forall₂ R items [value] → ∃ item, items = [item] ∧ R item value := by
    intro items related
    cases related with
    | cons head tail => cases tail; exact ⟨_, rfl, head⟩
  obtain ⟨item, rest, related⟩ := singleton ending
  exact ⟨left.take right.length, item, by rw [← rest, List.take_append_drop], beginning, related⟩

private theorem paired_imp_member {α β : Type} {R S : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right)
    (change : ∀ a b, b ∈ right → R a b → S a b) : List.Forall₂ S left right := by
  induction paired with
  | nil => exact .nil
  | @cons a b left right related rest ih =>
    exact .cons (change a b (by simp) related)
      (ih (fun a b member related => change a b (List.mem_cons_of_mem _ member) related))

theorem ScopeFrameStack.split {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current) :
    ∃ prior frame, compiler.frames.val = prior ++ [frame] ∧
      List.Forall₂ (FrameScope locals compiler) parents prior ∧ FrameScope locals compiler current frame := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := paired_last (List.Forall₂.flip stack.frames)
  exact ⟨prior, frame, frames, List.Forall₂.flip paired, shape⟩

theorem ScopeFrameStack.transport {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (frames : after.frames.val = before.frames.val)
    (preserve : ∀ scope frame, FrameScope locals before scope frame → FrameScope locals after scope frame) :
    ScopeFrameStack locals after parents current := by
  refine ⟨stack.nested, ?_⟩
  rw [frames]
  exact stack.frames.imp preserve

theorem ScopeFrameStack.extend {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (frames : after.frames.val = before.frames.val) (suffix : List Bytecode)
    (code : after.function.code.val = before.function.code.val ++ suffix)
    (maps : before.function.controls.val.length ≤ after.function.controls.val.length) :
    ScopeFrameStack locals after parents current :=
  stack.transport frames (fun _ _ shape => shape.extend suffix code maps)

theorem ScopeFrameStack.advance {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (instruction : instr) : ScopeFrameStack locals compiler parents (current.advance instruction) := by
  obtain ⟨prior, frame, frames, paired, shape⟩ := stack.split
  refine ⟨stack.nested.advance instruction, ?_⟩
  rw [frames]
  exact List.rel_append paired (.cons (shape.advance instruction) .nil)

theorem ScopeFrameStack.push {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (child : SourceScope) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = before.frames.val ++ [frame])
    (preserve : ∀ scope oldFrame, FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame)
    (fresh : FrameScope locals after child frame) (order : current.bodyPc ≤ child.entry)
    (geometry : child.entry ≤ child.bodyPc) :
    ScopeFrameStack locals after (parents ++ [current]) child := by
  refine ⟨.push stack.nested child order geometry, ?_⟩
  rw [frames]
  exact List.rel_append (stack.frames.imp preserve) (.cons fresh .nil)

/-- Closing the inner frame restores its paired parent and its source geometry. -/
theorem ScopeFrameStack.pop {A : Type} {locals parents parent current}
    {before after : runtime.compiler.FunctionCompiler A}
    (stack : ScopeFrameStack locals before (parents ++ [parent]) current)
    (frame : runtime.compiler.Frame) (frames : before.frames.val = after.frames.val ++ [frame])
    (preserve : ∀ scope oldFrame, oldFrame ∈ after.frames.val →
      FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame) :
    ScopeFrameStack locals after parents parent := by
  obtain ⟨prior, currentFrame, split, paired, shape⟩ := stack.split
  have same : prior = after.frames.val ∧ currentFrame = frame := by
    simpa using split.symm.trans frames
  rw [same.1] at paired
  exact ⟨stack.nested.pop, paired_imp_member paired preserve⟩

theorem ScopeFrameStack.distinct_guard {A : Type} {locals parents current}
    {compiler : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals compiler parents current)
    (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame]) (guard : Usize) (found : frame.if_pc = some guard) :
    ∀ other ∈ prior, other.if_pc ≠ some guard := by
  obtain ⟨actualPrior, actualFrame, actualFrames, paired, shape⟩ := stack.split
  have equal : actualPrior = prior ∧ actualFrame = frame := by
    simpa using actualFrames.symm.trans frames
  rcases equal with ⟨rfl, rfl⟩
  exact stack.nested.distinct_guard (paired.imp (fun _ _ h => h.toScopeFrameShape))
    shape.toScopeFrameShape guard found
theorem ScopeFrameStack.initial {A : Type} {locals returns}
    {compiler : runtime.compiler.FunctionCompiler A} (frame : runtime.compiler.Frame)
    (frames : compiler.frames.val = [frame])
    (shape : FrameScope locals compiler (SourceScope.initial returns) frame) :
    ScopeFrameStack locals compiler [] (SourceScope.initial returns) := by
  refine ⟨.initial returns, ?_⟩
  rw [frames]
  exact .cons shape .nil

/-- Replace the active frame after transporting its suspended ancestors. This
covers ELSE, whose new body entry is later but whose source entry is unchanged. -/
theorem ScopeFrameStack.replace_current {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (next : SourceScope) (prior : List runtime.compiler.Frame) (frame : runtime.compiler.Frame)
    (frames : after.frames.val = prior ++ [frame])
    (retained : List.Forall₂ (FrameScope locals after) parents prior)
    (fresh : FrameScope locals after next frame) (entry : next.entry = current.entry)
    (geometry : next.entry ≤ next.bodyPc) : ScopeFrameStack locals after parents next := by
  refine ⟨stack.nested.change_current next entry geometry, ?_⟩
  rw [frames]
  exact List.rel_append retained (.cons fresh .nil)
private theorem paired_set_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (before after : β)
    (found : right[index]? = some before) (change : ∀ a, R a before → R a after) :
    List.Forall₂ R left (right.set index after) := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right related rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst b
      exact .cons (change a related) rest
    | succ index => exact .cons related (ih index found)

/-- Recording a branch changes only its selected forward frame's fixups and
exit liveness; its source scope and nesting geometry remain paired. -/
theorem ScopeFrameStack.record_branch {A : Type} {locals parents current}
    {before after : runtime.compiler.FunctionCompiler A} (stack : ScopeFrameStack locals before parents current)
    (index : Nat) (frame : runtime.compiler.Frame) (fixups : alloc.vec.Vec Usize)
    (found : before.frames.val[index]? = some frame) (forward : frame.kind ≠ .Loop)
    (frames : after.frames.val = before.frames.val.set index {frame with fixups, end_reachable := true})
    (preserve : ∀ scope oldFrame, FrameScope locals before scope oldFrame → FrameScope locals after scope oldFrame) :
    ScopeFrameStack locals after parents current := by
  refine ⟨stack.nested, ?_⟩
  rw [frames]
  exact paired_set_right (stack.frames.imp preserve) index frame _ found
    (fun _ shape => shape.record_branch fixups forward)
end Itasca.Runtime.Code
