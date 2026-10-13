import Itasca.Wasm2.FixedOperands
import Itasca.Visitor.Basic

/-!
# Fixed operand effects that carry an immediate

`carryFixed` applies `readFixed` and then returns an already parsed immediate. Its segment,
completeness and visitor-runner lemmas (`carryFixed.segment`, `carryFixed.complete`,
`carryFixed.run`) are the shared interface for the SIMD lane, constant, shuffle and memory readers.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Simd

/-- Applies a fixed operand effect and returns the already parsed immediate. -/
def carryFixed {A : Type} (a : A) (st : code.OpIterState) (inputs : List types.ValueType)
    (output : Option types.ValueType) : Result (core.result.Result A error.OpError × code.OpIterState) := do
  let (r, s) ← readFixed st inputs output
  match r with
  | .Err e => .ok (.Err e, s)
  | .Ok _ => .ok (.Ok a, s)

theorem carryFixed.segment {A : Type} (a : A) (st : code.OpIterState)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (outer segment : List code.StackType)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max) :
    carryFixed a st inputs output ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.pos = st.pos ∧
      ∃ after, r.2.vals.val = outer ++ after ∧ after.length ≤ segment.length + 1 ∧
        (∀ value, r.1 = .Ok value → value = a ∧
          FixedEffect (Control.polymorphic st) segment inputs output after) ⦄ := by
  obtain ⟨⟨res, s⟩, hr, hc, hp, after, hv, hl, he⟩ := WP.spec_imp_exists
    (readFixed.segment st inputs output outer segment hv hb hsize)
  cases res with
  | Err e => simpa [carryFixed, hr] using ⟨hc, hp, after, hv, hl⟩
  | Ok u =>
    cases u
    simp only [carryFixed, hr, bind_ok]
    exact ⟨hc, hp, after, hv, hl, fun _ h => by cases h; exact ⟨rfl, he rfl⟩⟩

theorem carryFixed.complete {A : Type} (a : A) (st : code.OpIterState)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (outer segment : List code.StackType) (front : List valtype)
    (hv : st.vals.val = outer ++ segment) (hb : (Control.base st).val = outer.length)
    (hsize : st.vals.val.length < Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st) segment (front ++ inputTypes inputs)) :
    ∃ s after, carryFixed a st inputs output = .ok (.Ok a, s) ∧
      s.ctrls = st.ctrls ∧ s.pos = st.pos ∧ s.vals.val = outer ++ after ∧
      after.length ≤ segment.length + 1 ∧
      Sequence.Realizes (Control.polymorphic st) after (front ++ outputTypes output) := by
  obtain ⟨s, after, hr, hc, hp, hv, hl, ht⟩ := readFixed.complete st inputs output
    outer segment front hv hb hsize ht
  exact ⟨s, after, by simp [carryFixed, hr], hc, hp, hv, hl, ht⟩

/-- Returning a decoded payload commutes with the visitor's fixed stack runner. -/
theorem carryFixed.run {A V : Type} (a : A) (st : code.OpIterState)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (hook : V → code.OpIterState → A → Result (core.result.Result Unit error.VisitError × V))
    (v : V) :
    CoreVisitor.run (carryFixed a st inputs output) hook v =
      CoreVisitor.run (readFixed st inputs output) (fun v s _ => hook v s a) v := by
  simp only [carryFixed, CoreVisitor.run, Std.bind_assoc, Std.uncurry]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


end Itasca.Wasm2.Simd
