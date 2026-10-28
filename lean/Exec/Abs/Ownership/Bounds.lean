import Exec.Abs.Results
namespace Itasca.Runtime.Abs.Ownership

/-- Source function and external references use distinct issued address spaces. -/
structure Bounds where
  functions : Nat
  externs : Nat

/-- Only non-null references carry an ownership obligation. -/
def ValueOwned (bound : Bounds) : val → Prop
  | .REF_FUNC_ADDR address => address < bound.functions
  | .REF_HOST_ADDR address => address < bound.externs
  | _ => True

def ValuesOwned (bound : Bounds) (values : List val) : Prop := ∀ value ∈ values, ValueOwned bound value

def FrameOwned (bound : Bounds) (f : AFrame) : Prop :=
  ValuesOwned bound f.locals ∧ ValuesOwned bound f.vals

def StateOwned (bound : Bounds) (s : AState) : Prop :=
  ValuesOwned bound s.results ∧ ∀ f ∈ s.frames, FrameOwned bound f

private theorem values_subset {bound before after} (bounded : ValuesOwned bound before)
    (subset : ∀ value ∈ after, value ∈ before) : ValuesOwned bound after :=
  fun value member => bounded value (subset value member)

@[simp] theorem valuesOwned_nil (bound : Bounds) : ValuesOwned bound [] := by simp [ValuesOwned]

@[simp] theorem valuesOwned_append {bound left right} :
    ValuesOwned bound (left ++ right) ↔ ValuesOwned bound left ∧ ValuesOwned bound right := by
  simp only [ValuesOwned, List.mem_append]
  constructor
  · intro h; exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨hl, hr⟩ v (hv | hv)
    · exact hl v hv
    · exact hr v hv

@[simp] theorem valuesOwned_cons {bound value rest} :
    ValuesOwned bound (value :: rest) ↔ ValueOwned bound value ∧ ValuesOwned bound rest := by
  simp [ValuesOwned]

 theorem ValuesOwned.take {bound values} (bounded : ValuesOwned bound values) (count : Nat) :
    ValuesOwned bound (values.take count) := values_subset bounded (fun _ member => List.mem_of_mem_take member)

 theorem ValuesOwned.drop {bound values} (bounded : ValuesOwned bound values) (count : Nat) :
    ValuesOwned bound (values.drop count) := values_subset bounded (fun _ member => List.mem_of_mem_drop member)

 theorem ValuesOwned.set {bound values value} (bounded : ValuesOwned bound values)
    (allowed : ValueOwned bound value) (index : Nat) : ValuesOwned bound (values.set index value) := by
  induction values generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using valuesOwned_cons.mpr ⟨allowed, (valuesOwned_cons.mp bounded).2⟩
    | succ index =>
      simpa using valuesOwned_cons.mpr ⟨(valuesOwned_cons.mp bounded).1, ih (valuesOwned_cons.mp bounded).2 index⟩

 theorem ValuesOwned.pop {bound values rest value} (bounded : ValuesOwned bound values)
    (popped : Abs.pop values = some (rest, value)) : ValuesOwned bound rest ∧ ValueOwned bound value := by
  unfold Abs.pop at popped
  split at popped
  · contradiction
  next last tail equal =>
    have reversed : values = (last :: tail).reverse := by rw [← equal, List.reverse_reverse]
    rw [reversed, List.reverse_cons] at bounded
    cases popped
    simpa using bounded

 theorem defaultValue_ownership {bound ty value} (created : defaultValue ty = some value) :
    ValueOwned bound value := by
  cases ty <;> simp [defaultValue] at created <;> subst value <;> trivial

 theorem defaultLocals_ownership {bound locals values} (created : defaultLocals locals = some values) :
    ValuesOwned bound values := by
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
          exact valuesOwned_cons.mpr ⟨defaultValue_ownership first, ih tail⟩

 theorem ownership_advance {bound s f rest next}
    (results : ValuesOwned bound s.results) (frame : FrameOwned bound f)
    (frames : ∀ item ∈ rest, FrameOwned bound item)
    (step : advance s f rest = .next next) : StateOwned bound next := by
  cases step
  exact ⟨results, by simpa using And.intro frame frames⟩

 theorem ownership_return {bound s f rest next}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : returnFrame s f rest = .next next) : StateOwned bound next := by
  unfold returnFrame at step
  split at step
  · split at step
    · cases step
      exact ⟨frame.2.drop _, by simp⟩
    next original caller callers =>
      have callerBound := frames caller (by simp)
      apply ownership_advance (step := step) results
      · exact ⟨callerBound.1, valuesOwned_append.mpr ⟨callerBound.2, frame.2.drop _⟩⟩
      · exact fun item member => frames item (by simp [member])
  · contradiction

 theorem ownership_branch {bound s f rest next depth}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : branch s f rest depth = .next next) : StateOwned bound next := by
  unfold branch at step
  split at step
  · contradiction
  next target found =>
    split at step
    · apply ownership_advance (step := step) results ?_ frames
      exact ⟨frame.1, valuesOwned_append.mpr ⟨frame.2.take _, frame.2.drop _⟩⟩
    · contradiction

 theorem ownership_enter {bound s f rest next ty body after loop}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : enterLabel s f rest ty body after loop = .next next) : StateOwned bound next := by
  simp only [enterLabel] at step
  repeat' first | split at step | contradiction
  all_goals
    apply ownership_advance (step := step) results ?_ frames
    exact frame

 theorem ownership_call {bound s f rest next index after}
    (frame : FrameOwned bound f) (frames : ∀ item ∈ rest, FrameOwned bound item)
    (results : ValuesOwned bound s.results)
    (step : call s f rest index after = .next next) : StateOwned bound next := by
  simp only [call] at step
  repeat' first | split at step | contradiction
  cases step
  refine ⟨results, ?_⟩
  simp only [List.mem_cons, forall_eq_or_imp]
  refine ⟨⟨valuesOwned_append.mpr ⟨frame.2.drop _, ?_⟩, valuesOwned_nil _⟩, ⟨frame.1, frame.2.take _⟩, frames⟩
  apply defaultLocals_ownership
  assumption

end Itasca.Runtime.Abs.Ownership
