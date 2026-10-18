import Exec.Abs.Results
namespace Exec.Abs

/-- Reference addresses carried by values fit a fixed address space. -/
def ReferenceBound (bound : Nat) : val → Prop
  | .REF_FUNC_ADDR address | .REF_HOST_ADDR address => address < bound
  | _ => True

def ValuesBound (bound : Nat) (values : List val) : Prop := ∀ value ∈ values, ReferenceBound bound value

def FrameReferencesBound (bound : Nat) (f : AFrame) : Prop :=
  ValuesBound bound f.locals ∧ ValuesBound bound f.vals

def StateReferencesBound (bound : Nat) (s : AState) : Prop :=
  ValuesBound bound s.results ∧ ∀ f ∈ s.frames, FrameReferencesBound bound f

private theorem values_subset {bound before after} (bounded : ValuesBound bound before)
    (subset : ∀ value ∈ after, value ∈ before) : ValuesBound bound after :=
  fun value member => bounded value (subset value member)

@[simp] theorem valuesBound_nil (bound : Nat) : ValuesBound bound [] := by simp [ValuesBound]

@[simp] theorem valuesBound_append {bound left right} :
    ValuesBound bound (left ++ right) ↔ ValuesBound bound left ∧ ValuesBound bound right := by
  simp only [ValuesBound, List.mem_append]
  constructor
  · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hl, hr⟩ v (hv | hv)
    · exact hl v hv
    · exact hr v hv

@[simp] theorem valuesBound_cons {bound value rest} :
    ValuesBound bound (value :: rest) ↔ ReferenceBound bound value ∧ ValuesBound bound rest := by
  simp [ValuesBound]

 theorem ValuesBound.take {bound values} (bounded : ValuesBound bound values) (count : Nat) :
    ValuesBound bound (values.take count) := values_subset bounded (fun _ member => List.mem_of_mem_take member)

 theorem ValuesBound.drop {bound values} (bounded : ValuesBound bound values) (count : Nat) :
    ValuesBound bound (values.drop count) := values_subset bounded (fun _ member => List.mem_of_mem_drop member)

 theorem ValuesBound.set {bound values value} (bounded : ValuesBound bound values)
    (allowed : ReferenceBound bound value) (index : Nat) : ValuesBound bound (values.set index value) := by
  induction values generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using valuesBound_cons.mpr ⟨allowed, (valuesBound_cons.mp bounded).2⟩
    | succ index =>
      simpa using valuesBound_cons.mpr ⟨(valuesBound_cons.mp bounded).1, ih (valuesBound_cons.mp bounded).2 index⟩

 theorem ValuesBound.pop {bound values rest value} (bounded : ValuesBound bound values)
    (popped : Abs.pop values = some (rest, value)) : ValuesBound bound rest ∧ ReferenceBound bound value := by
  unfold Abs.pop at popped
  split at popped
  · contradiction
  next last tail equal =>
    have reversed : values = (last :: tail).reverse := by rw [← equal, List.reverse_reverse]
    rw [reversed, List.reverse_cons] at bounded
    cases popped
    simpa using bounded

 theorem defaultValue_reference_bound {bound ty value} (created : defaultValue ty = some value) :
    ReferenceBound bound value := by
  cases ty <;> simp [defaultValue] at created <;> subst value <;> trivial

 theorem defaultLocals_reference_bound {bound locals values} (created : defaultLocals locals = some values) :
    ValuesBound bound values := by
  induction locals generalizing values with
  | nil => simp [defaultLocals] at created; subst values; simp
  | cons item locals ih =>
    cases item with
    | LOCAL ty =>
      cases first : defaultValue ty with
      | none => simp [defaultLocals, first] at created
      | some value =>
        cases tail : defaultLocals locals with
        | none => simp [defaultLocals, first, tail] at created
        | some rest =>
          simp [defaultLocals, first, tail] at created
          subst values
          exact valuesBound_cons.mpr ⟨defaultValue_reference_bound first, ih tail⟩

 theorem references_advance {bound s f rest next}
    (results : ValuesBound bound s.results) (frame : FrameReferencesBound bound f)
    (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (step : advance s f rest = .next next) : StateReferencesBound bound next := by
  cases step
  exact ⟨results, by simpa using And.intro frame frames⟩

 theorem references_return {bound s f rest next}
    (frame : FrameReferencesBound bound f) (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (results : ValuesBound bound s.results)
    (step : returnFrame s f rest = .next next) : StateReferencesBound bound next := by
  unfold returnFrame at step
  split at step
  · split at step
    · cases step
      exact ⟨frame.2.drop _, by simp⟩
    next original caller callers =>
      have callerBound := frames caller (by simp)
      apply references_advance (step := step) results
      · exact ⟨callerBound.1, valuesBound_append.mpr ⟨callerBound.2, frame.2.drop _⟩⟩
      · exact fun item member => frames item (by simp [member])
  · contradiction

 theorem references_branch {bound s f rest next depth}
    (frame : FrameReferencesBound bound f) (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (results : ValuesBound bound s.results)
    (step : branch s f rest depth = .next next) : StateReferencesBound bound next := by
  unfold branch at step
  split at step
  · contradiction
  next target found =>
    split at step
    · apply references_advance (step := step) results ?_ frames
      exact ⟨frame.1, valuesBound_append.mpr ⟨frame.2.take _, frame.2.drop _⟩⟩
    · contradiction

 theorem references_enter {bound s f rest next ty body after loop}
    (frame : FrameReferencesBound bound f) (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (results : ValuesBound bound s.results)
    (step : enterLabel s f rest ty body after loop = .next next) : StateReferencesBound bound next := by
  simp only [enterLabel] at step
  repeat' first | split at step | contradiction
  all_goals
    apply references_advance (step := step) results ?_ frames
    exact frame

 theorem references_call {bound s f rest next index after}
    (frame : FrameReferencesBound bound f) (frames : ∀ item ∈ rest, FrameReferencesBound bound item)
    (results : ValuesBound bound s.results)
    (step : call s f rest index after = .next next) : StateReferencesBound bound next := by
  simp only [call] at step
  repeat' first | split at step | contradiction
  cases step
  refine ⟨results, ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨⟨valuesBound_append.mpr ⟨frame.2.drop _, ?_⟩, valuesBound_nil _⟩, ⟨frame.1, frame.2.take _⟩, frames⟩
  apply defaultLocals_reference_bound
  assumption

end Exec.Abs
