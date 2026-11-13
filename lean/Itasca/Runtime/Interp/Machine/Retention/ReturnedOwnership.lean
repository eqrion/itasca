import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Bound
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.Interp.Control.NormalizeCompose
import Itasca.Runtime.SourceMachine.Ownership.Extension
import Itasca.Runtime.Interp.Relations.Normalization
import Itasca.Runtime.Interp.Calls.ReturnRefinement

/-!
Sections, each formerly its own module: CodeBounds, Ownership, ReturnedOwnership.
-/

/-! ## CodeBounds -/

section

/-!
Code-size preservation is separate from value provenance and allowed syntax.

Main declarations: `FrameBoundClosure`. A direct consumer is `Interp.Machine.Control.BranchIfOwned`.
-/

namespace Itasca.Runtime.Interp

/-- Code-size preservation is separate from value provenance and allowed syntax. -/
def FrameBoundClosure (before after : SourceMachine.AFrame) : Prop :=
  ∀ bound, SourceMachine.FrameCodeBound bound before → SourceMachine.FrameCodeBound bound after

theorem FrameBoundClosure.refl (f : SourceMachine.AFrame) : FrameBoundClosure f f := fun _ h => h

theorem FrameBoundClosure.tail (f : SourceMachine.AFrame) (op : instr) (after : List instr)
    (locals values : List val) :
    FrameBoundClosure {f with code := op::after} {f with code := after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  change sizeOf after ≤ bound
  simp only [List.cons.sizeOf_spec] at size
  omega

theorem FrameBoundClosure.replace (f : SourceMachine.AFrame) (op next : instr) (after : List instr)
    (locals values : List val) (smaller : sizeOf next ≤ sizeOf op) :
    FrameBoundClosure {f with code := op::after} {f with code := next::after,locals,vals := values} := by
  rintro bound ⟨size,labels⟩
  refine ⟨?_,labels⟩
  simp only [List.cons.sizeOf_spec] at size ⊢
  omega

theorem FrameBoundClosure.branch (f : SourceMachine.AFrame) (depth : Nat) (label : SourceMachine.Label)
    (lookup : f.labels[depth]? = some label) (values : List val) :
    FrameBoundClosure f {f with code := label.cont++label.after,labels := f.labels.drop (depth+1),vals := values} := by
  rintro bound ⟨size,labels⟩
  exact ⟨labels label (List.mem_of_getElem? lookup),fun next member => labels next (List.mem_of_mem_drop member)⟩

theorem FrameBoundClosure.state {before after} (closure : FrameBoundClosure before after)
    {bound s ambient rest} (bounded : SourceMachine.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.CodeBound bound ⟨s,ambient,after::rest,[]⟩ :=
  SourceMachine.bound_replace_frame bounded (closure bound (bounded.frames before (List.mem_cons_self ..)))

theorem ErasedSteps.code_bound {count before after} (steps : ErasedSteps count before after)
    {bound s ambient rest} (bounded : SourceMachine.CodeBound bound ⟨s,ambient,before::rest,[]⟩) :
    SourceMachine.CodeBound bound ⟨s,ambient,after::rest,[]⟩ := steps.closure.code_bound bounded
end Itasca.Runtime.Interp

end

/-! ## Ownership -/

section

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

end

/-! ## ReturnedOwnership -/

section

/-!
Returning retains only the existing result suffix and the saved callers; no returned reference can acquire a different owner.

Main declarations: `returned_state_owned`. A direct consumer is `Interp.Machine.Memory`.
-/

namespace Itasca.Runtime.Interp
open SourceMachine.Ownership

/-- Returning retains only the existing result suffix and the saved callers;
no returned reference can acquire a different owner. -/
theorem returned_state_owned {s : store} {ambient : frame} {f : SourceMachine.AFrame} {rest : List SourceMachine.AFrame}
    (results : List val) (subset : ∀ value ∈ results, value ∈ f.vals) :
    ∀ bounds, CoreOwned bounds ⟨s,ambient,f::rest,[]⟩ →
      CoreOwned bounds (returnedState s ambient rest results) := by
  intro bounds owned
  have first := owned.values.2 f (by simp)
  have values : ValuesOwned bounds results := fun value member => first.2 value (subset value member)
  cases rest with
  | nil => exact ⟨⟨values,by simp [returnedState]⟩,owned.globals⟩
  | cons caller rest =>
    have saved := owned.values.2 caller (by simp)
    refine ⟨⟨values_owned_nil _,?_⟩,owned.globals⟩
    intro item member
    change item ∈ {caller with vals := caller.vals++results}::rest at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨saved.1,values_owned_append.mpr ⟨saved.2,values⟩⟩
    · exact owned.values.2 item (by simp [member])
end Itasca.Runtime.Interp

end
