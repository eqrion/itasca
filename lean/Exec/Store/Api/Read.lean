import Exec.Store.Api.Api

namespace Exec.Store
open Aeneas Aeneas.Std

/-- The observable table size agrees with the decoded reference sequence. -/
theorem table_size_read {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (index : Usize)
    (hindex : index.val < s.tables.length)
    (hsize : (s.tables.val[index.val]).elements.length ≤ U32.max) :
    runtime.store.Store.table_size ops s ⟨s.id, index⟩ ⦃ answer =>
      ∃ size : U32, answer = .Ok size ∧
        size.val = (decodeTable (s.tables.val[index.val])).REFS.length ⦄ := by
  unfold runtime.store.Store.table_size
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨table, htable⟩
  simp [lift]
  simp only [decodeTable, List.length_map]
  scalar_tac

end Exec.Store
