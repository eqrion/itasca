import Itasca.Generated.Types

/-!
Allocator content-preservation and normal-return laws, with a separate allocation-availability premise. Compiler and runtime proofs distinguish valid allocation behavior from requests being granted.
-/

namespace Itasca.Runtime.Platform
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

/-- Every reserve request whose resulting logical length is within `bound`
succeeds. The bound is independent of any client computation or its result;
clients must prove that their requests fit it. Native capacity is unmodeled. -/
def AllocationAvailable {A : Type} (ops : runtime.platform.Alloc A) (bound : Nat) : Prop :=
  ∀ (T : Type) (values : alloc.vec.Vec T) (additional : Usize),
    values.val.length + additional.val ≤ bound →
    ops.reserve values additional = .ok (true, values)

end Itasca.Runtime.Platform
