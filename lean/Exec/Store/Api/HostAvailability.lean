import Exec.Store.Invariant.InternTypes
import Exec.Platform.Availability

namespace Exec.Store
open Aeneas Aeneas.Std

/-- An independently present signature is found without allocating or changing
the store. No successful API invocation is assumed. -/
theorem intern_type_present {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (type : Itasca.types.FuncType)
    (present : type ∈ store.types.val) :
    runtime.store.Store.intern_type memory allocator store type ⦃ out =>
      ∃ signature, out = (.Ok signature,store) ∧ store.types.val[signature.val]? = some type ⦄ := by
  obtain ⟨scanned,actual,index,same,bound,prior,found⟩ :=
    WP.spec_imp_exists (intern_scan store type 0#usize (by scalar_tac) (by simp))
  rw [same] at actual
  have inside : index.val < store.types.length := by
    by_contra outside
    have last : index.val = store.types.length := by omega
    have absent : type ∉ store.types.val := by simpa [last] using prior
    exact absent present
  have numericInside : index < alloc.vec.Vec.len store.types := by scalar_tac
  have lookup : store.types.val[index.val]? = some type := by
    rcases found with found | last
    · exact found
    · omega
  unfold runtime.store.Store.intern_type
  rw [actual]
  simp [scanState]
  split
  · exact ⟨index,rfl,lookup⟩
  · rename_i outside
    exact False.elim (outside numericInside)

/-- Publication succeeds when a signature is present, an object slot remains,
and the actual function-vector reserve request is independently available. -/
theorem define_host_present_available {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (type : Itasca.types.FuncType)
    (identity : U64) (present : type ∈ store.types.val)
    (room : objectCount store < store.limits.max_objects.val)
    (bound : Nat) (available : Platform.AllocationAvailable allocator bound)
    (request : store.funcs.length + 1 ≤ bound) :
    runtime.store.Store.define_host_with memory allocator store type identity ⦃ out =>
      ∃ signature functions,
        out = (.Ok ⟨store.id,alloc.vec.Vec.len store.funcs⟩,{store with funcs := functions}) ∧
        functions.val = store.funcs.val ++ [⟨signature,.Host identity⟩] ∧
        store.types.val[signature.val]? = some type ⦄ := by
  have objectBound : objectCount store ≤ Usize.max := by scalar_tac
  have capacity : store.funcs.length < Usize.max := by
    unfold objectCount at room
    scalar_tac
  obtain ⟨out,actual,signature,interned,lookup⟩ := WP.spec_imp_exists
    (intern_type_present memory allocator store type present)
  rw [interned] at actual
  unfold runtime.store.Store.define_host_with
  rw [actual]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with room_spec memory store objectBound as ⟨checked,checkedEq⟩
  rw [checkedEq,if_pos room]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [Platform.reserve_available allocator available store.funcs 1#usize (by simpa using request)]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step as ⟨functions,appended⟩
  exact ⟨signature,functions,rfl,appended,lookup⟩

end Exec.Store
