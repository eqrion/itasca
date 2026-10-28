import Exec.Interp.Memory.MemoryMutation
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- SIMD retains the store or replaces the opaque buffer of one issued memory
without changing its length. Source semantics separately constrain its bytes. -/
def SimdStoreMutation {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) : Prop :=
  after = before ∨ ∃ address object, before.memories.val[address.index.val]? = some object ∧
    MemoryMutation view before after address object

end Itasca.Runtime.Interp
