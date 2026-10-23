import Exec.Theorems.Composition.Cumulative.CumulativeMutationCertified
import Exec.Theorems.Composition.Certified.CertifiedCumulativeSegments
import Exec.Theorems.Composition.TableInstructionCertified
import Exec.Interp.Memory.MemoryMutation
import Exec.Store.Invariant.ObjectExtension
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp
theorem memory_mutation_cumulative {M : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedCumulativeStore view code before)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (issued : before.memories.val[address.index.val]? = some object)
    (mutation : Interp.MemoryMutation view before after address object) :
    CumulativeStoreMutation view code before after := by
  obtain ⟨buffer,rfl,lengthEq⟩ := mutation
  have inBounds : address.index.val < before.memories.length := (List.getElem?_eq_some_iff.mp issued).1
  have found : before.memories.val[address.index.val] = object := (List.getElem?_eq_some_iff.mp issued).2
  let after := {before with memories := before.memories.set address.index {object with buf := buffer}}
  have shape : Store.Shape view after := by
    apply certified.shape.memory_replace_same_length address.index inBounds
    · simpa only [found] using lengthEq
    · simp only [found]
  have sourceSyntax : Store.StoreSyntax code after := certified.storeSyntax
  have oldWf := Store.decodeStore_wf view code before certified.shape certified.storeSyntax
  have newWf := Store.decodeStore_wf view code after shape sourceSyntax
  have oldMemoryWf : wf_meminst (Store.decodeMemory view object) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (certified.shape.memories object (List.mem_of_getElem? issued)).2.1
      scalar_tac
    · exact Store.decodeBytes_wf _
  have newMemoryWf : wf_meminst (Store.decodeMemory view {object with buf := buffer}) := by
    apply wf_meminst.meminst_case_
    · apply wf_memtype.memtype_case_0
      apply Store.decodeLimits_wf
      have bound := (certified.shape.memories object (List.mem_of_getElem? issued)).2.1
      simp only [lengthEq]
      scalar_tac
    · exact Store.decodeBytes_wf _
  have objectExtension := Store.decodeMemory_extends view object {object with buf := buffer}
    rfl (Nat.le_of_eq lengthEq.symm) oldMemoryWf newMemoryWf
  have extension : Extend_store (Store.decodeStore view code before) (Store.decodeStore view code after) := by
    unfold after at newWf ⊢
    rw [Store.decodeStore_memory_update view code before
      (before.memories.set address.index {object with buf := buffer})] at newWf ⊢
    simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
    apply Spec.extend_store_set_mem _ _ _ oldWf
    · simpa only [Store.decodeStore] using newWf
    · intro bound
      simpa only [Store.decodeStore,found,
        getElem!_pos (before.memories.val.map (Store.decodeMemory view)) address.index.val
          (by simpa only [List.length_map] using inBounds),List.getElem_map] using objectExtension
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shape,⟨certified.segmentBounds.elements,certified.segmentBounds.data⟩,extension,⟨rfl,rfl⟩,rfl⟩
theorem table_mutation_cumulative {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedCumulativeStore view code before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    CumulativeStoreMutation view code before after := by
  obtain ⟨shape,extension⟩ := table_mutation_extends view code before after certified.shape certified.storeSyntax
    address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  exact ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,shape,⟨certified.segmentBounds.elements,certified.segmentBounds.data⟩,extension,⟨rfl,rfl⟩,rfl⟩

theorem segment_mutation_cumulative {M : Type} {view : M → Slice U8}
    {code : CodeInterpretation} {before after : runtime.store.Store M}
    (certified : CertifiedCumulativeStore view code before)
    (metadata : SegmentObjectMetadata view before after) (shape : Shape view after) :
    CumulativeStoreMutation view code before after := by
  have preserved := certified.segments metadata shape
  exact ⟨⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩,
    by rw [metadata.space.frozen],shape,preserved.1.segmentBounds,preserved.2,⟨metadata.space.elements,metadata.space.datas⟩,by rw [metadata.space.frozen]⟩
end Exec.Theorems
