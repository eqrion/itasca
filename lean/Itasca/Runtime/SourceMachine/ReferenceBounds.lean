import Itasca.Runtime.SourceMachine.Results
namespace Itasca.Runtime.SourceMachine

/-- Reference addresses carried by values fit a fixed address space. -/
def ReferenceBound (bound : Nat) : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address < bound
  | _ => True

def ValuesBound (bound : Nat) (values : List val) : Prop := ∀ value ∈ values, ReferenceBound bound value

def FrameReferencesBound (bound : Nat) (f : AFrame) : Prop :=
  ValuesBound bound f.locals ∧ ValuesBound bound f.vals

@[simp] theorem values_bound_nil (bound : Nat) : ValuesBound bound [] := by simp [ValuesBound]

@[simp] theorem values_bound_append {bound left right} :
    ValuesBound bound (left ++ right) ↔ ValuesBound bound left ∧ ValuesBound bound right := by
  simp only [ValuesBound, List.mem_append]
  constructor
  · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hl, hr⟩ v (hv | hv)
    · exact hl v hv
    · exact hr v hv

@[simp] theorem values_bound_cons {bound value rest} :
    ValuesBound bound (value :: rest) ↔ ReferenceBound bound value ∧ ValuesBound bound rest := by
  simp [ValuesBound]

 theorem ValuesBound.set {bound values value} (bounded : ValuesBound bound values)
    (allowed : ReferenceBound bound value) (index : Nat) : ValuesBound bound (values.set index value) := by
  induction values generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using values_bound_cons.mpr ⟨allowed, (values_bound_cons.mp bounded).2⟩
    | succ index =>
      simpa using values_bound_cons.mpr ⟨(values_bound_cons.mp bounded).1, ih (values_bound_cons.mp bounded).2 index⟩

end Itasca.Runtime.SourceMachine
