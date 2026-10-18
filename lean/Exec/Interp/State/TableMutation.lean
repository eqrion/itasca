import Exec.Interp.State.TableSource
import Exec.Interp.Relations.FrameStoreMetadata
namespace Exec.Interp
open Aeneas Aeneas.Std Exec.Store

/-- A table content update retains the object's reference type, maximum and
length; every word is either retained or the explicit replacement reference. -/
def TableMutation {M : Type} (before after : runtime.store.Store M)
    (address : runtime.TableAddr) (object : runtime.store.Table) (replacement : U64) : Prop :=
  ∃ words, after = {before with tables := before.tables.set address.index {object with elements := words}} ∧
    words.length = object.elements.length ∧
    ∀ word ∈ words.val, word ∈ object.elements.val ∨ word = replacement

theorem TableMutation.frame_metadata {M : Type} {before after : runtime.store.Store M} {address object replacement}
    (mutation : TableMutation before after address object replacement) : FrameStoreMetadata before after := by
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- The actual table write either has the precise content update or leaves
both execution and store untouched on the source bounds trap. -/
theorem table_set_mutation {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (index value table : U32) (inst : runtime.store.Instance)
    (address : runtime.TableAddr) (object : runtime.store.Table) (position : U32)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (valueBound : base.val+value.val < exec.slots.length)
 :
    runtime.interp.admin_table_set memory hooks floats allocator exec store instanceIndex base index value table ⦃ out =>
      out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      ((out.1 = .Ok () ∧ TableMutation store out.2.2 address object exec.slots.val[base.val+value.val]!) ∨
       (out.1 = .Err (.Trap .TableOutOfBounds) ∧ out.2.2 = store)) ⦄ := by
  apply WP.spec_mono (table_set_effect memory hooks floats allocator exec store instanceIndex base index value table
    inst address object position found mapped issued input indexBound valueBound)
  intro out effect
  split at effect
  · rw [effect]
    refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,Or.inl ⟨rfl,object.elements.set (UScalar.cast .Usize position) exec.slots.val[base.val+value.val]!,rfl,by simp,?_⟩⟩
    intro word member
    simp only [alloc.vec.Vec.set_val_eq] at member
    exact List.mem_or_eq_of_mem_set member
  · rw [effect]
    exact ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩⟩
end Exec.Interp
