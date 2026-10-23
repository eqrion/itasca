import Exec.Store.Preparation.PreparedInitializers
import Exec.Store.Invariant.TypeStagingLoop
import Exec.Store.Invariant.FunctionStagingLoop
import Exec.Store.Api.TableStagingLoop
import Exec.Store.Api.MemoryStagingLoop

namespace Exec.Store
open Aeneas Aeneas.Std

theorem typeParts_inj {M : Type} (a b : runtime.store.Store M)
    (s t : core.result.Result Unit runtime.ExecError) (i j : runtime.store.ModuleInst) :
    typeParts a s i = typeParts b t j ↔ a = b ∧ s = t ∧ i = j := by
  cases i; cases j
  simp [typeParts]

/-- Normalize the flattened tuple returned by the actual preparation loops.
The computation and its checked total postcondition remain explicit. -/
theorem preparation_result {M R : Type}
    (parts : runtime.store.Store M → core.result.Result Unit runtime.ExecError → runtime.store.ModuleInst → R)
    (injective : ∀ a b s t i j, parts a s i = parts b t j → a = b ∧ s = t ∧ i = j)
    (computation : Result R) (post : runtime.store.Store M → runtime.store.ModuleInst → core.result.Result Unit runtime.ExecError → Prop)
    (checked : computation ⦃ out => ∃ store inst status, out = parts store status inst ∧ post store inst status ⦄)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (status : core.result.Result Unit runtime.ExecError)
    (run : computation = .ok (parts store status inst)) : post store inst status := by
  rw [run] at checked
  simp only [WP.spec_ok] at checked
  obtain ⟨after, next, result, eq, property⟩ := checked
  obtain ⟨rfl, rfl, rfl⟩ := injective _ _ _ _ _ _ eq
  exact property

end Exec.Store
