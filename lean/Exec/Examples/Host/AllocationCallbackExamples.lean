import Exec.Theorems.Host.Callbacks.AllocationCallbacks
import Exec.Store.Api.HostAvailability

namespace Exec.Theorems.AllocationCallbacks
open Aeneas Aeneas.Std

theorem world_sound {M A : Type} (memory : runtime.platform.MemoryBuffer M) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (select : U64 → Slice runtime.Value → Program)
    (view : M → Slice U8) : HostWorldSound (platform memory allocator select) view (ExecutableInv view) :=
  HostWorldSound.of_fixed (sound memory allocator allocation select view)

/-- Publication-capable callbacks derive all raw/result laws alongside the
source-store obligation, including the branch that traps after interning. -/
theorem callback_package {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (select : U64 → Slice runtime.Value → Program) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (token : Unit) (store : runtime.store.Store M) (held : ExecutableInv view code store)
    (identity : U64) (args results : Slice runtime.Value) :
    (platform memory allocator select).call_host token store identity args results ⦃ answer =>
      ExecutableInv view code answer.2.2.1 ∧ Interp.FrameStorePrefix store answer.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code answer.2.2.1) ∧
      answer.2.2.1.externs = store.externs ∧
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value ⦄ := by
  unfold platform
  step with (select identity args).correct memory allocator allocation view code store held
    as ⟨answer,_,fresh,metadata,extension,externs,issued⟩
  exact ⟨fresh,metadata,extension,externs,issued⟩

/-- Independent signature membership, object room, and reserve availability
produce actual callback publication, with no assumed successful definition. -/
theorem publication_available {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (type : Itasca.types.FuncType) (identity : U64)
    (present : type ∈ store.types.val) (room : Store.objectCount store < store.limits.max_objects.val)
    (bound : Nat) (available : Platform.AllocationAvailable allocator bound)
    (request : store.funcs.length + 1 ≤ bound) :
    (Program.defineHost type identity (.base (.terminal (.returned (Slice.new _))))).run memory allocator store
      ⦃ answer => answer.1 = .Ok () ∧ ExecutableInv view code answer.2.1 ∧
        Store_ok (Store.decodeStore view code answer.2.1) ∧
        ∃ signature functions, answer.2.1 = {store with funcs := functions} ∧
          functions.val = store.funcs.val ++ [⟨signature,.Host identity⟩] ∧
          store.types.val[signature.val]? = some type ⦄ := by
  obtain ⟨out,actual,signature,functions,same,appended,lookup⟩ := WP.spec_imp_exists
    (Store.define_host_present_available memory allocator store type identity present room bound available request)
  rw [same] at actual
  have fresh := ExecutableInv.define_host_certified memory allocator allocation view code store held type identity
  rw [actual,WP.spec_ok] at fresh
  simp only [Program.run,actual,bind_ok,StoreCallbacks.Program.run,PureCallbacks.Program.evaluate]
  exact WP.spec.ret ⟨rfl,fresh.1,fresh.1.source_typed,signature,functions,rfl,appended,lookup⟩

private theorem definition_traps {M : Type} {store after : runtime.store.Store M}
    {type : Itasca.types.FuncType} {identity : U64} {status values}
    (source : Returns (.defineHost type identity (.base (.terminal .trapped))) store status after values) :
    status = .Err .Trap := by
  cases source with
  | published effect tail =>
    cases tail with
    | base returned =>
      cases returned with
      | terminal ended => cases ended; rfl
  | refused => rfl

/-- This finite script always traps after its definition attempt. Any interned
signature or published host entry remains covered by the source-typed invariant. -/
theorem publication_then_trap {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (allocation : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (store : runtime.store.Store M)
    (held : ExecutableInv view code store) (type : Itasca.types.FuncType) (identity : U64) :
    (Program.defineHost type identity (.base (.terminal .trapped))).run memory allocator store
      ⦃ answer => answer.1 = .Err .Trap ∧ ExecutableInv view code answer.2.1 ∧
        Store_ok (Store.decodeStore view code answer.2.1) ⦄ := by
  apply WP.spec_mono ((Program.defineHost type identity (.base (.terminal .trapped))).correct
    memory allocator allocation view code store held)
  intro answer post
  exact ⟨definition_traps post.1,post.2.1,post.2.1.source_typed⟩

end Exec.Theorems.AllocationCallbacks
