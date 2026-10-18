import Exec.Generated.Types

namespace Exec.Platform
open Aeneas Aeneas.Std

/-- Allocation may report either answer but must return normally and preserve
all modeled vector contents. Native capacity is outside Aeneas's vector model. -/
def AllocCorrect {A : Type} (ops : runtime.platform.Alloc A) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    ops.reserve values additional ⦃ result => result.2 = values ⦄

theorem AllocCorrect.reserve_eq {A T : Type} {ops : runtime.platform.Alloc A}
    (h : AllocCorrect ops) (values : alloc.vec.Vec T) (additional : Usize) :
    ∃ answer, ops.reserve values additional = .ok (answer, values) := by
  obtain ⟨⟨answer, after⟩, hr, hp⟩ := WP.spec_imp_exists (h T values additional)
  dsimp only at hp
  subst after
  exact ⟨answer, hr⟩

end Exec.Platform
