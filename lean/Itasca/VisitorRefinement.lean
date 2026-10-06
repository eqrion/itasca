import Itasca.VisitorRunTrace

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- Every ordinary callback return can be reproduced with its exact outcome and
related visitor state. This is conditional and requires no termination premise. -/
def Refines {V W : Type} (visitor : code.OpVisitor V) (replacement : code.OpVisitor W)
    (related : V → W → Prop) : Prop :=
  ∀ v w event reply v', related v w → invoke visitor v event = .ok (reply, v') →
    ∃ w', invoke replacement w event = .ok (reply, w') ∧ related v' w'

theorem instrument_refines {V : Type} (visitor : code.OpVisitor V)
    (initial : List Observation) :
    Refines visitor (instrument visitor)
      (fun v w => v = w.1 ∧ ∃ added, w.2 = initial ++ added) := by
  rintro v ⟨w, log⟩ event reply v' ⟨rfl, added, rfl⟩ h
  exact ⟨(v', initial ++ added ++ [⟨event, reply⟩]), by simp [h],
    rfl, added ++ [⟨event, reply⟩], by simp⟩

theorem instrument_refines_back {V : Type} (visitor : code.OpVisitor V) :
    Refines (instrument visitor) visitor (fun w v => w.1 = v) := by
  rintro ⟨v, log⟩ w event reply ⟨v', log'⟩ rfl h
  have hi := (record_ok_iff log event _ reply v' log').mp (by simpa using h)
  exact ⟨v', hi.1, rfl⟩

end Itasca.VisitorTrace

namespace Itasca.CoreVisitor

open VisitorTrace

/-- Hook refinement lifts through handler failure and callback acceptance or rejection. -/
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
