import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableBuild
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameElse
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

private theorem paired_set_right {α β : Type} {R : α → β → Prop} {left right}
    (paired : List.Forall₂ R left right) (index : Nat) (before after : β)
    (found : right[index]? = some before) (change : ∀ a, R a before → R a after) :
    List.Forall₂ R left (right.set index after) := by
  induction paired generalizing index with
  | nil => simp at found
  | @cons a b left right related rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      subst b
      exact .cons (change a related) rest
    | succ index => exact .cons related (ih index found)

/-- Every arm preserves the original source-scope geometry. Forward arms only
add a relocation and record exit liveness; loop frames remain untouched. -/
theorem TableTargetCode.scope_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) (locals : List valtype) (scopes : List SourceScope)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val) :
    List.Forall₂ (ScopeFrameShape locals) scopes after.frames.val := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => simpa only [frames] using paired
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    rw [frames]
    exact paired_set_right paired index.val frame _ lookup (fun _ shape => shape.record_branch fixups kind)

theorem TableTargetsBuilt.scope_shapes {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) (locals : List valtype) (scopes : List SourceScope)
    (paired : List.Forall₂ (ScopeFrameShape locals) scopes before.frames.val) :
    List.Forall₂ (ScopeFrameShape locals) scopes after.frames.val := by
  induction built with
  | nil => exact paired
  | cons _ _ _ _ _ _ effect rest ih => exact ih (effect.scope_shapes locals scopes paired)

/-- All emitted arms keep the physical control-stack length fixed. -/
theorem TableTargetCode.frame_length {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depth : U32}
    (effect : TableTargetCode before after depth) : after.frames.val.length = before.frames.val.length := by
  cases effect with
  | loop index frame source lookup position kind operands code frames => rw [frames]
  | forward index frame source fixups site lookup position kind operands code frames appended sitePosition =>
    simp only [frames,List.length_set]

theorem TableTargetsBuilt.frame_length {A : Type}
    {before after : runtime.compiler.FunctionCompiler A} {depths targets : List U32}
    (built : TableTargetsBuilt before after depths targets) : after.frames.val.length = before.frames.val.length := by
  induction built with
  | nil => rfl
  | cons _ _ _ _ _ _ effect rest ih => exact ih.trans effect.frame_length
end Itasca.Runtime.Compiler
