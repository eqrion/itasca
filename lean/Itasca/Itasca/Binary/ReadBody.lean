import Itasca.Binary.ReadInstruction
import Itasca.Results.Definitions.Validation

namespace Itasca.Binary.Source
open Aeneas.Std WebAssembly

private theorem eraseEnd {t} (h : token t = .end_) : t = .end_ := by cases t <;> cases h <;> rfl
private theorem eraseElse {t} (h : token t = .else_) : t = .else_ := by cases t <;> cases h <;> rfl

private theorem blockHeader {t bt} (h : token t = .block bt) :
    ∃ v, t = .block v ∧ Body.blockType v = bt := by
  cases t <;> cases h <;> exact ⟨_, rfl, rfl⟩

private theorem loopHeader {t bt} (h : token t = .loop bt) :
    ∃ v, t = .loop v ∧ Body.blockType v = bt := by
  cases t <;> cases h <;> exact ⟨_, rfl, rfl⟩

private theorem ifHeader {t bt} (h : token t = .if_ bt) :
    ∃ v, t = .if_ v ∧ Body.blockType v = bt := by
  cases t <;> cases h <;> exact ⟨_, rfl, rfl⟩

private theorem readEmits {ts ops} (h : WebAssembly.Binary.Emits ts ops) :
    ∀ {xs}, xs.map token = ts → Body.Emits xs ops := by
  induction h with
  | nil =>
    intro xs eq
    have := List.map_eq_nil_iff.mp eq
    subst xs
    exact .nil
  | simple _ hs ih =>
    intro xs eq
    obtain ⟨pre, last, rfl, hp, hl⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨t, rfl, ht⟩ := List.map_eq_singleton_iff.mp hl
    cases hs with
    | plain _ wf =>
      cases t <;> cases ht
      exact .simple (ih hp) (.plain _ wf)
  | block bt _ _ ih0 ih1 =>
    intro xs eq
    obtain ⟨_, _, rfl, eq1, hend⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨_, rfl, hendToken⟩ := List.map_eq_singleton_iff.mp hend
    obtain rfl := eraseEnd hendToken
    obtain ⟨_, _, rfl, eq2, hthen⟩ := List.map_eq_append_iff.mp eq1
    obtain ⟨_, _, rfl, eq3, hheader⟩ := List.map_eq_append_iff.mp eq2
    obtain ⟨_, rfl, hheaderToken⟩ := List.map_eq_singleton_iff.mp hheader
    obtain ⟨v, rfl, rfl⟩ := blockHeader hheaderToken
    exact .block v (ih0 eq3) (ih1 hthen)
  | loop bt _ _ ih0 ih1 =>
    intro xs eq
    obtain ⟨_, _, rfl, eq1, hend⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨_, rfl, hendToken⟩ := List.map_eq_singleton_iff.mp hend
    obtain rfl := eraseEnd hendToken
    obtain ⟨_, _, rfl, eq2, hthen⟩ := List.map_eq_append_iff.mp eq1
    obtain ⟨_, _, rfl, eq3, hheader⟩ := List.map_eq_append_iff.mp eq2
    obtain ⟨_, rfl, hheaderToken⟩ := List.map_eq_singleton_iff.mp hheader
    obtain ⟨v, rfl, rfl⟩ := loopHeader hheaderToken
    exact .loop v (ih0 eq3) (ih1 hthen)
  | ifElse bt _ _ _ ih0 ih1 ih2 =>
    intro xs eq
    obtain ⟨_, _, rfl, eq1, hend⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨_, rfl, hendToken⟩ := List.map_eq_singleton_iff.mp hend
    obtain rfl := eraseEnd hendToken
    obtain ⟨_, _, rfl, eq2, helseBody⟩ := List.map_eq_append_iff.mp eq1
    obtain ⟨_, _, rfl, eq3, helse⟩ := List.map_eq_append_iff.mp eq2
    obtain ⟨_, rfl, helseToken⟩ := List.map_eq_singleton_iff.mp helse
    obtain rfl := eraseElse helseToken
    obtain ⟨_, _, rfl, eq4, hthen⟩ := List.map_eq_append_iff.mp eq3
    obtain ⟨_, _, rfl, eq5, hheader⟩ := List.map_eq_append_iff.mp eq4
    obtain ⟨_, rfl, hheaderToken⟩ := List.map_eq_singleton_iff.mp hheader
    obtain ⟨v, rfl, rfl⟩ := ifHeader hheaderToken
    exact .ifElse v (ih0 eq5) (ih1 hthen) (ih2 helseBody)
  | ifEnd bt _ _ ih0 ih1 =>
    intro xs eq
    obtain ⟨_, _, rfl, eq1, hend⟩ := List.map_eq_append_iff.mp eq
    obtain ⟨_, rfl, hendToken⟩ := List.map_eq_singleton_iff.mp hend
    obtain rfl := eraseEnd hendToken
    obtain ⟨_, _, rfl, eq2, hthen⟩ := List.map_eq_append_iff.mp eq1
    obtain ⟨_, _, rfl, eq3, hheader⟩ := List.map_eq_append_iff.mp eq2
    obtain ⟨_, rfl, hheaderToken⟩ := List.map_eq_singleton_iff.mp hheader
    obtain ⟨v, rfl, rfl⟩ := ifHeader hheaderToken
    exact .ifEnd v (ih0 eq3) (ih1 hthen)

theorem readRep {R : α → List U8 → Prop} {S : β → List UInt8 → Prop} (f : α → β)
    (step : ∀ {y bs}, S y bs → ∃ x, f x = y ∧ R x (readerBytes bs))
    {ys bs} (h : WebAssembly.Binary.Rep S ys bs) :
    ∃ xs, xs.map f = ys ∧ Rep R xs (readerBytes bs) := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hv _ ih =>
    obtain ⟨x, rfl, hx⟩ := step hv
    obtain ⟨xs, rfl, hs⟩ := ih
    exact ⟨x :: xs, rfl, by simp only [readerBytes, List.map_append]; exact .cons hx hs⟩

theorem readBody {ops bs} (h : WebAssembly.Binary.BodyBytes ops bs) :
    CodeEntry.BodyBytes ops (readerBytes bs) := by
  obtain ⟨ts, hr, inner, rfl, he⟩ := h
  obtain ⟨xs, eq, hx⟩ := readRep token @readToken hr
  refine ⟨xs, hx, ?_⟩
  obtain ⟨pre, last, rfl, hp, hl⟩ := List.map_eq_append_iff.mp eq
  obtain ⟨t, rfl, ht⟩ := List.map_eq_singleton_iff.mp hl
  obtain rfl := eraseEnd ht
  exact ⟨pre, rfl, readEmits he hp⟩

end Itasca.Binary.Source
