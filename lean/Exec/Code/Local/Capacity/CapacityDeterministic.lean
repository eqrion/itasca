import Exec.Code.Local.Source.ValidatedStacks
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A canonical empty-visitor validation run has a unique operand trace. -/
theorem ValidatedStacksWasm1.deterministic {data env ctx bt st samples other}
    (left : ValidatedStacksWasm1 data env ctx bt st samples)
    (right : ValidatedStacksWasm1 data env ctx bt st other) : samples = other := by
  induction left generalizing other with
  | done typed closed finished =>
    cases right with
    | done => rfl
    | step typed pending start advance read rest =>
      have bound := pending.inbounds
      simp only [start, finished, Slice.len_val] at bound
      omega
  | @step st next out samples typed pending start advance read rest ih =>
    cases right with
    | done typed closed finished =>
      have bound := pending.inbounds
      simp only [start, finished, Slice.len_val] at bound
      omega
    | @step _ next' out' samples' typed' pending' start' advance' read' rest' =>
      have nextEq : next' = next := UScalar.eq_of_val_eq (by omega)
      subst next'
      have same : out' = out := by
        have readLeft := read
        simp only [start] at readLeft
        simp only [start'] at read'
        rw [readLeft] at read'
        simpa only [Result.ok.injEq, Prod.mk.injEq, true_and, and_true] using read'.symm
      subst out'
      exact congrArg (List.cons st.vals.val) (ih rest')
/-- A canonical empty-visitor validation run has a unique operand trace. -/
theorem ValidatedStacksWasm2.deterministic {data env ctx index st samples other}
    (left : ValidatedStacksWasm2 data env ctx index st samples)
    (right : ValidatedStacksWasm2 data env ctx index st other) : samples = other := by
  induction left generalizing other with
  | done typed closed finished =>
    cases right with
    | done => rfl
    | step typed pending start advance read rest =>
      have bound := pending.inbounds
      simp only [start, finished, Slice.len_val] at bound
      omega
  | @step st next out samples typed pending start advance read rest ih =>
    cases right with
    | done typed closed finished =>
      have bound := pending.inbounds
      simp only [start, finished, Slice.len_val] at bound
      omega
    | @step _ next' out' samples' typed' pending' start' advance' read' rest' =>
      have nextEq : next' = next := UScalar.eq_of_val_eq (by omega)
      subst next'
      have same : out' = out := by
        have readLeft := read
        simp only [start] at readLeft
        simp only [start'] at read'
        rw [readLeft] at read'
        simpa only [Result.ok.injEq, Prod.mk.injEq, true_and, and_true] using read'.symm
      subst out'
      exact congrArg (List.cons st.core.vals.val) (ih rest')
theorem ProfileValidatedStacks.deterministic {profile data env ctx index samples other}
    (left : ProfileValidatedStacks profile data env ctx index samples)
    (right : ProfileValidatedStacks profile data env ctx index other) : samples = other := by
  cases profile with
  | Wasm1 => exact ValidatedStacksWasm1.deterministic left right
  | Wasm2 => exact ValidatedStacksWasm2.deterministic left right
end Exec.Code
