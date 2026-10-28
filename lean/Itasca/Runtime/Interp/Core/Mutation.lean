import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Interp.State.GlobalMutation
import Itasca.Runtime.Abs.Ownership.Core
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- A live source value is already present in an operand or local region, or
in the invocation's final result vector. -/
def CoreLiveValue (source : Abs.AState) (value : val) : Prop :=
  value ∈ source.results ∨ ∃ f ∈ source.frames, value ∈ f.locals ∨ value ∈ f.vals

theorem CoreLiveValue.owned {bounds source value} (present : CoreLiveValue source value)
    (owned : Abs.Ownership.CoreOwned bounds source) : Abs.Ownership.ValueOwned bounds value := by
  rcases present with member | ⟨f,frame,member | member⟩
  · exact owned.values.1 value member
  · exact (owned.values.2 f frame).1 value member
  · exact (owned.values.2 f frame).2 value member

/-- Concrete scalar execution changes only payloads of existing objects.
Global writes carry their original live source value, retaining provenance. -/
inductive CoreStoreMutation {M : Type} (view : M → Slice U8) (source : Abs.AState)
    (before : runtime.store.Store M) : runtime.store.Store M → Prop where
  | unchanged : CoreStoreMutation view source before before
  | memory {after address object} (issued : before.memories.val[address.index.val]? = some object)
      (mutation : MemoryMutation view before after address object) : CoreStoreMutation view source before after
  | global {after value} (live : CoreLiveValue source value) (wellFormed : wf_val value)
      (mutation : GlobalMutation before after value) : CoreStoreMutation view source before after

end Itasca.Runtime.Interp
