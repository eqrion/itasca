import Itasca.Visitor.EventMeaning
import Itasca.Binary.Wasm1.Encoding

/-!
# Callback traces and byte provenance

Describes callback traces without mentioning the extracted code. `LabelsAt` and `PartialTable`
relate the label callbacks of an unfinished `br_table` to the bytes they decode, and `Outcomes`
relates observations to the validator result.
-/

open Aeneas Aeneas.Std

namespace Itasca.VisitorTrace

/-- The result of validating an instruction or a body. -/
abbrev BodyResult := core.result.Result Unit error.OpError

/-- Converts a callback reply to a validator result: a rejection becomes `OpError.Visitor`. -/
def outcome : VisitResult → BodyResult
  | .Ok () => .Ok ()
  | .Err e => .Err (.Visitor e)

/-- Every observation in the list was accepted. -/
def AllAccepted (observations : List Observation) : Prop :=
  ∀ observation ∈ observations, observation.outcome = .Ok ()

theorem AllAccepted.append {xs ys} (hx : AllAccepted xs) (hy : AllAccepted ys) :
    AllAccepted (xs ++ ys) := by
  intro o ho
  exact (List.mem_append.mp ho).elim (hx o) (hy o)

/-- The observations are consistent with a result. A success has only accepted callbacks. A visitor
error is either the reply of a rejecting last callback that follows accepted ones, or follows only
accepted callbacks. Any other error follows only accepted callbacks. -/
def Outcomes (observations : List Observation) : BodyResult → Prop
  | .Ok () => AllAccepted observations
  | .Err (.Visitor e) => AllAccepted observations ∨ ∃ before event,
      observations = before ++ [⟨event, .Err e⟩] ∧ AllAccepted before
  | .Err _ => AllAccepted observations

theorem Outcomes.of_accepted {observations} (h : AllAccepted observations) (result : BodyResult) :
    Outcomes observations result := by
  cases result with
  | Ok u => cases u; exact h
  | Err e => cases e <;> first | exact h | exact Or.inl h

theorem Outcomes.empty (result : BodyResult) : Outcomes [] result :=
  .of_accepted (by simp [AllAccepted]) result

theorem Outcomes.single (event : Event) (reply : VisitResult) :
    Outcomes [⟨event, reply⟩] (outcome reply) := by
  cases reply with
  | Ok u => cases u; simp [Outcomes, outcome, AllAccepted]
  | Err e => exact Or.inr ⟨[], event, rfl, by simp [AllAccepted]⟩

theorem Outcomes.prepend {before observations result}
    (hp : AllAccepted before) (h : Outcomes observations result) :
    Outcomes (before ++ observations) result := by
  cases result with
  | Ok u => cases u; exact hp.append h
  | Err e =>
      cases e <;> try (exact hp.append h)
      rcases h with h | h
      · exact Or.inl (hp.append h)
      obtain ⟨xs, event, rfl, hb⟩ := h
      exact Or.inr ⟨before ++ xs, event, by simp [List.append_assoc], hp.append hb⟩

/-- The observations of the `br_table` vector entries, with their label depths in order and the
byte cursor after each entry. The relation is defined by the binary encoding alone. -/
inductive LabelsAt (data : Slice U8) : Usize → List Observation → List U32 → Usize → Prop where
  | nil (pos : Usize) : LabelsAt data pos [] [] pos
  | cons {pos depth st reply observations depths last} :
      Leb128.Decoded data pos depth st.pos →
      LabelsAt data st.pos observations depths last →
      LabelsAt data pos (⟨.op st (.br_table_label depth), reply⟩ :: observations)
        (depth :: depths) last

/-- The callbacks of a `br_table` that stopped before its closing callback. They cover some or all
of the vector entries, including an entry whose target merge failed after its callback ran. -/
def PartialTable (data : Slice U8) (start : Usize) (observations : List Observation) : Prop :=
  ∃ pos count first depths last,
    Wasm1.BytesAt data start [0x0E#u8] pos ∧
    Leb128.Decoded data pos count first ∧
    LabelsAt data first observations depths last ∧ depths.length ≤ count.val

end Itasca.VisitorTrace
