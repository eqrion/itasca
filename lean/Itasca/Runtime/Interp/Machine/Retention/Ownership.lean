import Itasca.Runtime.SourceMachine.Ownership.Core
import Itasca.Runtime.Interp.Relations.Normalization

/-!
Value provenance is independent of source syntax and typing.

Main declarations: `FrameOwnershipClosure`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp
open SourceMachine.Ownership

/-- Value provenance is independent of source syntax and typing. -/
def FrameOwnershipClosure (before after : SourceMachine.AFrame) : Prop :=
  ∀ bounds, FrameOwned bounds before → FrameOwned bounds after

theorem FrameOwnershipClosure.refl (f : SourceMachine.AFrame) : FrameOwnershipClosure f f := fun _ h => h

theorem FrameOwnershipClosure.trans {before middle after}
    (first : FrameOwnershipClosure before middle) (second : FrameOwnershipClosure middle after) :
    FrameOwnershipClosure before after := fun bound h => second bound (first bound h)

theorem FrameOwnershipClosure.subsets {before after : SourceMachine.AFrame}
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

theorem FrameOwnershipClosure.same_values {before after : SourceMachine.AFrame}
    (locals : after.locals = before.locals) (values : after.vals = before.vals) :
    FrameOwnershipClosure before after := by
  intro bound owned
  simpa only [FrameOwned,locals,values] using owned

theorem FrameOwnershipClosure.drop (f : SourceMachine.AFrame) (before after : List instr)
    (front : List val) (value : val) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front } := by
  intro bounds owned
  exact ⟨owned.1,(values_owned_append.mp owned.2).1⟩

theorem FrameOwnershipClosure.local_get (f : SourceMachine.AFrame) (code : List instr)
    (index : Nat) (value : val) (lookup : f.locals[index]? = some value) :
    FrameOwnershipClosure f { f with code, vals := f.vals ++ [value] } := by
  intro bounds owned
  exact ⟨owned.1,values_owned_append.mpr ⟨owned.2,values_owned_cons.mpr
    ⟨owned.1 value (List.mem_of_getElem? lookup),values_owned_nil _⟩⟩⟩

theorem FrameOwnershipClosure.local_set (f : SourceMachine.AFrame) (before after : List instr)
    (front : List val) (value : val) (index : Nat) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front, locals := f.locals.set index value } := by
  intro bounds owned
  have split := values_owned_append.mp owned.2
  exact ⟨owned.1.set (split.2 value (by simp)) index,split.1⟩

theorem FrameOwnershipClosure.local_tee (f : SourceMachine.AFrame) (before after : List instr)
    (front : List val) (value : val) (index : Nat) :
    FrameOwnershipClosure { f with code := before, vals := front ++ [value] }
      { f with code := after, vals := front ++ [value], locals := f.locals.set index value } := by
  intro bounds owned
  exact ⟨owned.1.set (owned.2 value (by simp)) index,owned.2⟩

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
end Itasca.Runtime.Interp
