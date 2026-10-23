import Itasca.Visitor.RunTrace

/-!
# Callback refinement

`VisitorTrace.Refines` relates two visitors when every normally returning callback of one is
matched by the other with the same reply and a related state. `instrument_refines` and
`instrument_refines_back` show that the recording wrapper `instrument` refines and is refined by
the wrapped visitor, and `CoreVisitor.run.refines` lifts a refinement through one instruction
step. Covers both profiles.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- Every callback of `visitor` that returns normally is matched by a callback of `replacement`
with the same reply and a related state. No termination of either visitor is assumed. -/
def Refines {V W : Type} (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) : Prop :=
  ∀ v w event reply v', related v w → invoke visitor v event = .ok (reply, v') →
    ∃ w', invoke replacement w event = .ok (reply, w') ∧ related v' w'

/-- `instrument visitor` refines `visitor`. A state of `visitor` relates to an instrumented state
with the same first component and a log that extends `initial`. -/
theorem instrument_refines {V : Type} (visitor : code.OpVisitor V)
    (initial : List Observation) :
    Refines visitor (instrument visitor)
      (fun v w => v = w.1 ∧ ∃ added, w.2 = initial ++ added) := by
  rintro v ⟨w, log⟩ event reply v' ⟨rfl, added, rfl⟩ h
  exact ⟨(v', initial ++ added ++ [⟨event, reply⟩]), by simp [h],
    rfl, added ++ [⟨event, reply⟩], by simp⟩

end Itasca.VisitorTrace

namespace Itasca.CoreVisitor

open VisitorTrace

/-- A refinement of hooks lifts to `CoreVisitor.run`, whether the reader fails or the hook accepts
or rejects. -/
theorem run.refines {A V W : Type}
    (read : Result (core.result.Result A error.OpError × code.OpIterState))
    (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) (hrefines : Refines visitor replacement related)
    (event : code.OpIterState → A → Event)
    (v : V) (w : W) (hrelated : related v w)
    (res : core.result.Result Unit error.OpError) (st' : code.OpIterState) (v' : V)
    (h : run read (fun v st a => invoke visitor v (event st a)) v = .ok (res, st', v')) :
    ∃ w', run read (fun w st a => invoke replacement w (event st a)) w =
      .ok (res, st', w') ∧ related v' w' := by
  rcases (run.returned_iff _ _ _ _ _ _).mp h with
    ⟨err, hr, rfl, rfl⟩ | ⟨a, reply, hr, hv, rfl⟩
  · exact ⟨w, (run.returned_iff _ _ _ _ _ _).mpr (Or.inl ⟨err, hr, rfl, rfl⟩), hrelated⟩
  · obtain ⟨w', hw, hr'⟩ := hrefines v w (event st' a) reply v' hrelated hv
    exact ⟨w', (run.returned_iff _ _ _ _ _ _).mpr
      (Or.inr ⟨a, reply, hr, hw, rfl⟩), hr'⟩

end Itasca.CoreVisitor
