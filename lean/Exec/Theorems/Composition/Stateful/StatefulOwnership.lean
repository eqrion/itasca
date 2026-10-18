import Exec.Theorems.Composition.Core.CoreOwnership
import Exec.Abs.Stateful.Ownership
namespace Exec.Store
open Aeneas Aeneas.Std

theorem reference_value_owned {M : Type} (store : runtime.store.Store M)
    (type : Itasca.types.ElemType) (word : U64) (shape : ReferenceShape store type word) :
    Abs.Ownership.ValueOwned (ownershipBounds store) (val_ref (decodeRef type word)) := by
  cases type <;> unfold ReferenceShape at shape
  all_goals
    by_cases zero : word.val = 0
    · simp [decodeRef,zero,val_ref,Abs.Ownership.ValueOwned]
    · have bound := shape.resolve_left zero
      simpa only [decodeRef,if_neg zero,val_ref,Abs.Ownership.ValueOwned,ownershipBounds] using bound

theorem Shape.stateful_heap_owned {M : Type} {view : M → Slice U8} {store : runtime.store.Store M}
    (shape : Shape view store) (code : CodeInterpretation) :
    Abs.Ownership.StatefulHeapOwned (ownershipBounds store) (decodeStore view code store) := by
  refine ⟨shape.globals_owned code,?_,?_,?_⟩
  · intro object member reference present
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨word,wordMember,rfl⟩ := List.mem_map.mp present
    exact reference_value_owned store raw.ty word ((shape.tables raw rawMember).2.2 word wordMember)
  · intro object member reference present
    obtain ⟨raw,rawMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨word,wordMember,rfl⟩ := List.mem_map.mp present
    exact reference_value_owned store raw.ty word (shape.elements raw rawMember word wordMember)
  · simp [decodeStore,ownershipBounds]
end Exec.Store
namespace Exec.Theorems
open Aeneas Aeneas.Std

theorem stateful_entry_owned {M : Type} {view : M → Slice U8} {code : Store.CodeInterpretation}
    {store : runtime.store.Store M} (shape : Store.Shape view store)
    (ambient : frame) (address : funcaddr) (moduleInst : moduleinst) (results : List valtype)
    (body : List instr) (args : List runtime.Value) (locals : List «local») (defaults : List val)
    (owned : ∀ value ∈ args,Store.ValueInStore store value)
    (created : Abs.defaultLocals locals = some defaults) :
    Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      (Abs.entryState (Store.decodeStore view code store) ambient address moduleInst results body
        (args.map Interp.sourceValue) defaults) :=
  ⟨(core_entry_owned shape ambient address moduleInst results body args locals defaults owned created).values,
    shape.stateful_heap_owned code⟩
end Exec.Theorems
