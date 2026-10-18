import Exec.Abs.Ownership.Core
import Exec.Interp.Relations.Normalization
namespace Exec.Interp
open Abs.Ownership

/-- Value provenance is independent of source syntax and typing. -/
def FrameOwnershipClosure (before after : Abs.AFrame) : Prop :=
  ∀ bounds, FrameOwned bounds before → FrameOwned bounds after

theorem FrameOwnershipClosure.refl (f : Abs.AFrame) : FrameOwnershipClosure f f := fun _ h => h

theorem FrameOwnershipClosure.trans {before middle after}
    (first : FrameOwnershipClosure before middle) (second : FrameOwnershipClosure middle after) :
    FrameOwnershipClosure before after := fun bound h => second bound (first bound h)

theorem FrameOwnershipClosure.subsets {before after : Abs.AFrame}
    (locals : ∀ value ∈ after.locals, value ∈ before.locals ∨ value ∈ before.vals)
    (values : ∀ value ∈ after.vals, value ∈ before.locals ∨ value ∈ before.vals) :
    FrameOwnershipClosure before after := by
  intro bound owned
  constructor
  · intro value member
    rcases locals value member with h | h
    · exact owned.1 value h
    · exact owned.2 value h
  · intro value member
    rcases values value member with h | h
    · exact owned.1 value h
    · exact owned.2 value h

theorem FrameOwnershipClosure.same_values {before after : Abs.AFrame}
    (locals : after.locals = before.locals) (values : after.vals = before.vals) :
    FrameOwnershipClosure before after := by
  intro bound owned
  simpa only [FrameOwned,locals,values] using owned

theorem FrameOwnershipClosure.drop (f : Abs.AFrame) (before after : List instr)
    (front : List val) (value : val) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front } := by
  intro bounds owned
  exact ⟨owned.1,(valuesOwned_append.mp owned.2).1⟩

theorem FrameOwnershipClosure.branch (f : Abs.AFrame) (code : List instr)
    (labels : List Abs.Label) (height count : Nat) :
    FrameOwnershipClosure f { f with code, labels, vals := f.vals.take height ++ f.vals.drop count } := by
  intro bounds owned
  exact ⟨owned.1,valuesOwned_append.mpr ⟨owned.2.take _,owned.2.drop _⟩⟩

theorem FrameOwnershipClosure.local_get (f : Abs.AFrame) (code : List instr)
    (index : Nat) (value : val) (lookup : f.locals[index]? = some value) :
    FrameOwnershipClosure f { f with code, vals := f.vals ++ [value] } := by
  intro bounds owned
  exact ⟨owned.1,valuesOwned_append.mpr ⟨owned.2,valuesOwned_cons.mpr
    ⟨owned.1 value (List.mem_of_getElem? lookup),valuesOwned_nil _⟩⟩⟩

theorem FrameOwnershipClosure.local_set (f : Abs.AFrame) (before after : List instr)
    (front : List val) (value : val) (index : Nat) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front, locals := f.locals.set index value } := by
  intro bounds owned
  have split := valuesOwned_append.mp owned.2
  exact ⟨owned.1.set (split.2 value (by simp)) index,split.1⟩

theorem FrameOwnershipClosure.local_tee (f : Abs.AFrame) (before after : List instr)
    (front : List val) (value : val) (index : Nat) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front ++ [value], locals := f.locals.set index value } := by
  intro bounds owned
  exact ⟨owned.1.set (owned.2 value (by simp)) index,owned.2⟩

theorem FrameOwnershipClosure.state {before after} (closure : FrameOwnershipClosure before after)
    {bounds s ambient rest} (owned : CoreOwned bounds ⟨s,ambient,before :: rest,[]⟩) :
    CoreOwned bounds ⟨s,ambient,after :: rest,[]⟩ := by
  refine ⟨⟨owned.values.1,?_⟩,owned.globals⟩
  intro frame member
  rcases List.mem_cons.mp member with rfl | member
  · exact closure bounds (owned.values.2 _ (List.mem_cons_self ..))
  · exact owned.values.2 frame (List.mem_cons_of_mem _ member)

theorem ErasedStep.ownership {before after} (step : ErasedStep before after) :
    FrameOwnershipClosure before after := by
  cases step with
  | drop f after front value => exact FrameOwnershipClosure.drop f _ _ front value
  | _ => exact FrameOwnershipClosure.same_values rfl rfl

theorem ErasedSteps.ownership {count before after} (steps : ErasedSteps count before after) :
    FrameOwnershipClosure before after := by
  induction steps with
  | nil f => exact .refl f
  | cons step tail ih => exact step.ownership.trans ih
end Exec.Interp
