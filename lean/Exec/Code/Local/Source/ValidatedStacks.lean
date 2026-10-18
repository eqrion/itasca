import Exec.Representation.ValidatedStacks
import Exec.Code.Local.Relations.Common.EntryTypedSteps
import Exec.Code.Local.Relations.Control.ControlLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem maximumStackWords_member {samples stack} (member : stack ∈ samples) :
    stackWords stack ≤ maximumStackWords samples := by
  induction samples with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact Nat.le_max_left _ _
    · exact (ih member).trans (Nat.le_max_right _ _)

theorem observedHeight_stackWords (base : Nat) (stack : List code.StackType) :
    observedHeight base stack = base + stackWords stack := by
  induction stack generalizing base with
  | nil => simp [observedHeight,stackWords]
  | cons ty rest ih => simp [observedHeight,stackWords,ih,Nat.add_assoc]

theorem TypedRunWasm1.validated_samples {V : Type} {visitor : code.OpVisitor V}
    {data env ctx bt st before after}
    (run : TypedRunWasm1 visitor data env ctx bt st before after) :
    ∃ samples, ValidatedStacksWasm1 data env ctx bt st samples := by
  induction run with
  | done typed closed finished => exact ⟨_, .done typed closed finished⟩
  | @step st v next out middle final typed pending start advance called rest ih =>
    obtain ⟨samples, trace⟩ := ih
    refine ⟨_, .step typed pending start advance ?_ trace⟩
    exact code.step.accepted_erase visitor _ _ data env ctx _ v middle called

theorem TypedRunWasm2.validated_samples {V : Type} {visitor : code.OpVisitor V}
    {data env ctx index st before after}
    (run : TypedRunWasm2 visitor data env ctx index st before after) :
    ∃ samples, ValidatedStacksWasm2 data env ctx index st samples := by
  induction run with
  | done typed closed finished => exact ⟨_, .done typed closed finished⟩
  | @step st v next out middle final typed pending start advance called rest ih =>
    obtain ⟨samples, trace⟩ := ih
    refine ⟨_, .step typed pending start advance ?_ trace⟩
    obtain ⟨reply, erased⟩ := Wasm2.Visitor.step_transfer visitor
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts
      data env ctx ctx rfl index _ _ _ v () middle called
    cases reply
    exact erased
theorem witness_validated_stacks {V : Type} {visitor : code.OpVisitor V}
    {data env index start finish before after profile}
    (w : CodeEntry.Witness visitor data env index start finish before after profile) :
    ∃ samples, ProfileValidatedStacks profile w.body env w.ctx w.typeIdx samples := by
  have trace := witness_typed_steps w
  cases profile with
  | Wasm1 => exact trace.validated_samples
  | Wasm2 => exact trace.validated_samples
end Exec.Code
