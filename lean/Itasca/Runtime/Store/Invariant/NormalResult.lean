import Itasca.Runtime.Equations
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- An immediate normal return of a bind requires an immediate normal return
of its input and the same normal result from the continuation. Effects and
divergence cannot be discarded by binding. -/
theorem normal_bind_exists {α β : Type} (input : Result α) (next : α → Result β)
    (output : β) (run : Aeneas.Std.bind input next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | ret value => exact ⟨value, rfl, by simpa only [bind_ok] using run⟩
  | vis effect continuation => simp only [bind_vis, vis_not_ok] at run
  | div => simp only [bind_div, div_not_ok] at run

end Itasca.Runtime.Store
