import Itasca.Handler.Block
import Itasca.Handler.Unreachable
import Itasca.Spec.TypingInversion

/-!
# Typed prefixes and realized stacks

Relates the validator's operand stack (`code.StackType`, with `Bot` for unreachable code) to
declarative stacks. `Sequence.Realizes` says a declarative stack is a possible reading of a
validator stack, and `Sequence.TypedPrefix` says the instructions read so far type at every
realized stack. `TypedPrefix.append` extends a prefix with generated `Instr_ok` rules, and
`DeclarativeComplete.head_realizes` is the inverse used by completeness proofs.
-/

open Aeneas Aeneas.Std

namespace Itasca.Sequence

/-- A concrete operand has its translated type, and a `Bot` operand has any type. -/
def Accepts : code.StackType → valtype → Prop
  | .Val t, t' => t' = Translate.valueType t
  | .Bot, _ => True

/-- The SpecTec value types of a validator stack, with `Bot` as `BOT`. The top of the stack is on
the right, as in SpecTec. -/
def stackTypes : List code.StackType → List valtype :=
  List.map (fun t => match t with | .Val v => Translate.valueType v | .Bot => .BOT)

/-- A declarative stack `ts` realizes the validator stack `vals` of a frame. If the frame is
polymorphic (unreachable), `ts` may have an arbitrary prefix below the known operands. -/
def Realizes (polymorphic : Bool) (vals : List code.StackType) (ts : List valtype) : Prop :=
  ∃ front suffix, (polymorphic = false → front = []) ∧
    List.Forall₂ Accepts vals suffix ∧ ts = front ++ suffix

/-- A validator stack realizes its own translation. -/
theorem realizes_default (poly : Bool) (vals : List code.StackType) :
    Realizes poly vals (stackTypes vals) := by
  refine ⟨[], stackTypes vals, by simp, ?_, by simp⟩
  induction vals with
  | nil => exact .nil
  | cons t ts ih =>
    apply List.Forall₂.cons _ ih
    cases t <;> simp [Accepts]

theorem realizes_empty (ts : List valtype) : Realizes false [] ts ↔ ts = [] := by
  simp [Realizes]

theorem realizes_polymorphic_empty (ts : List valtype) : Realizes true [] ts := by
  exact ⟨ts, [], by simp, .nil, by simp⟩

/-- Pushing an accepted operand preserves `Realizes`. -/
theorem Realizes.snoc {poly : Bool} {vals : List code.StackType} {ts : List valtype}
    (h : Realizes poly vals ts) (t : code.StackType) (u : valtype) (ht : Accepts t u) :
    Realizes poly (vals ++ [t]) (ts ++ [u]) := by
  obtain ⟨front, suffix, hf, hs, rfl⟩ := h
  exact ⟨front, suffix ++ [u], hf, List.rel_append hs (.cons ht .nil), List.append_assoc ..⟩

/-- The instructions `ops` read so far in a frame are well-formed and have type `[] -> ts` for every
`ts` that realizes the frame's stack `vals`. This is a per-frame invariant. -/
structure TypedPrefix (C : context) (ops : List instr) (poly : Bool)
    (vals : List code.StackType) : Prop where
  wellFormed : Forall wf_instr ops
  typed : ∀ ts, Realizes poly vals ts →
    Instrs_ok C ops (.mk_functype (.mk_list []) (.mk_list ts))

/-- The empty prefix types the empty stack. -/
theorem TypedPrefix.empty (C : context) (hC : wf_context C) : TypedPrefix C [] false [] := by
  constructor
  · simp [Forall]
  · intro ts ht
    have hnil := (realizes_empty ts).mp ht
    subst ts
    exact .empty C hC

/-- Appends one instruction to a typed prefix using the generated `seq` rule, given that each
realized output stack has a realized input stack on which the instruction is typed. -/
theorem TypedPrefix.append {C : context} {ops : List instr} {poly poly' : Bool}
    {vals vals' : List code.StackType} (h : TypedPrefix C ops poly vals)
    (hC : wf_context C) (op : instr) (hwf : wf_instr op)
    (hstep : ∀ out, Realizes poly' vals' out → ∃ input, Realizes poly vals input ∧
      Instrs_ok C [op] (.mk_functype (.mk_list input) (.mk_list out))) :
    TypedPrefix C (ops ++ [op]) poly' vals' := by
  constructor
  · simpa [Forall, or_imp, forall_and] using And.intro h.wellFormed hwf
  · intro out hout
    obtain ⟨input, hin, hop⟩ := hstep out hout
    exact .seq C ops [op] [] out input (h.typed input hin) hop hC
      h.wellFormed (by simpa [Forall] using hwf)

end Itasca.Sequence

namespace Itasca

end Itasca

namespace Itasca.DeclarativeComplete

/-- `Accepts` is preserved by widening the declarative type. -/
theorem accepts_mono {t : code.StackType} {a b : valtype}
    (h : Sequence.Accepts t a) (hs : Valtype_sub a b) : Sequence.Accepts t b := by
  cases t with
  | Bot => trivial
  | Val t =>
    cases hs with
    | refl => exact h
    | bot => cases t <;> simp [Sequence.Accepts, Translate.valueType] at h

/-- Pointwise `Accepts` is preserved by widening the declarative types. -/
theorem accepts_list_mono {vals : List code.StackType} {a b : List valtype}
    (h : List.Forall₂ Sequence.Accepts vals a) (hs : List.Forall₂ Valtype_sub a b) :
    List.Forall₂ Sequence.Accepts vals b := by
  induction h generalizing b with
  | nil => cases hs; exact .nil
  | cons h ht ih =>
    cases hs with
    | cons hs ht' => exact .cons (accepts_mono h hs) (ih ht')

/-- Widening a declarative stack preserves `Realizes`. -/
theorem realizes_mono {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (h : Sequence.Realizes poly vals a)
    (hs : Resulttype_sub (.mk_list a) (.mk_list b)) : Sequence.Realizes poly vals b := by
  obtain ⟨front, suffix, hf, hv, rfl⟩ := h
  have hs := result_sub_iff.mp hs
  have hf' := List.forall₂_take front.length hs
  have ht' := List.forall₂_drop front.length hs
  simp only [List.take_left, List.drop_left] at hf' ht'
  refine ⟨b.take front.length, b.drop front.length, ?_, ?_, (List.take_append_drop _ _).symm⟩
  · intro hp
    simp [hf hp]
  · exact accepts_list_mono hv ht'

/-- If a stack realizing `vals` is the input of a typed non-empty sequence, then it realizes the
framed input of the head's primitive rule, and the framed output types the tail. -/
theorem head_realizes {C : context} {op : instr} {ops : List instr}
    {poly : Bool} {vals : List code.StackType} {a b : List valtype}
    (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C (op :: ops) (.mk_functype (.mk_list a) (.mk_list b))) :
    ∃ front ins outs,
      Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)) ∧
      Sequence.Realizes poly vals (front ++ ins) ∧
      Instrs_ok C ops (.mk_functype (.mk_list (front ++ outs)) (.mk_list b)) := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  exact ⟨front, ins, outs, hop, realizes_mono hr hin, hrest⟩

/-- If a stack realizing `vals` is the input of a typed empty sequence, the output realizes `vals`
too. -/
theorem empty_realizes {C : context} {poly : Bool} {vals : List code.StackType}
    {a b : List valtype} (hr : Sequence.Realizes poly vals a)
    (h : Instrs_ok C [] (.mk_functype (.mk_list a) (.mk_list b))) :
    Sequence.Realizes poly vals b := realizes_mono hr (empty_sub h)

end Itasca.DeclarativeComplete
