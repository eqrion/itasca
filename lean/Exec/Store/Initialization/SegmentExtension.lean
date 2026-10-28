import Exec.Store.Initialization.SegmentObjectMetadata
import Exec.Store.Invariant.FunctionTypingExtension
import Exec.Store.Invariant.Typing
import Exec.Spec.Mutation
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

private theorem mapped_objects {A B : Type} [Inhabited B] (f : A → B)
    (R : B → B → Prop) (xs ys : List A) (lengths : xs.length ≤ ys.length)
    (objects : ∀ (index : Nat) (old : A), xs[index]? = some old → ∃ fresh,
      ys[index]? = some fresh ∧ R (f old) (f fresh)) :
    Spec.ObjectsExtend R (xs.map f) (ys.map f) := by
  refine ⟨by simpa only [List.length_map] using lengths, ?_⟩
  intro index bound
  have room : index < xs.length := by simpa only [List.length_map] using bound
  have found : xs[index]? = some xs[index] := List.getElem?_eq_getElem room
  obtain ⟨fresh, lookup, relation⟩ := objects index xs[index] found
  simpa only [List.getElem!_eq_getElem?_getD, List.getElem?_map, found, lookup,
    Option.map_some, Option.getD_some] using relation

private theorem table_extension (before after : runtime.store.TableInst)
    (ty : after.ty = before.ty) (maximum : after.maximum = before.maximum)
    (length : after.elements.length = before.elements.length)
    (old : wf_tableinst (decodeTable before)) (fresh : wf_tableinst (decodeTable after)) :
    Extend_tableinst (decodeTable before) (decodeTable after) := by
  unfold decodeTable at old fresh ⊢
  rw [ty, maximum, length] at fresh ⊢
  simp only [decodeLimits_option] at old fresh ⊢
  exact .mk_Extend_tableinst _ _ _ _ _ _ (Nat.le_refl _)
    (by simpa only [List.length_map] using length.ge) old fresh

private theorem memory_extension {M : Type} (view : M → Slice U8) (before after : runtime.store.MemInst M)
    (maximum : after.maximum = before.maximum) (length : (view after.buf).length = (view before.buf).length)
    (old : wf_meminst (decodeMemory view before)) (fresh : wf_meminst (decodeMemory view after)) :
    Extend_meminst (decodeMemory view before) (decodeMemory view after) := by
  unfold decodeMemory at old fresh ⊢
  rw [maximum, length] at fresh ⊢
  simp only [decodeLimits_option] at old fresh ⊢
  exact .mk_Extend_meminst _ _ _ _ _ (Nat.le_refl _)
    (by simpa only [decodeBytes, List.length_map] using length.ge) old fresh

private theorem element_extension (before after : runtime.store.ElemInst)
    (ty : after.ty = before.ty) (contents : after.refs.val = before.refs.val ∨ after.refs.val = []) :
    Extend_eleminst (decodeElement before) (decodeElement after) := by
  unfold decodeElement
  rw [ty]
  apply Extend_eleminst.mk_Extend_eleminst
  rcases contents with same | empty
  · exact Or.inl (by rw [same])
  · exact Or.inr (by rw [empty]; rfl)

private theorem data_extension (before after : runtime.store.DataInst)
    (contents : after.bytes.val = before.bytes.val ∨ after.bytes.val = [])
    (old : wf_datainst (decodeData before)) (fresh : wf_datainst (decodeData after)) :
    Extend_datainst (decodeData before) (decodeData after) := by
  apply Extend_datainst.mk_Extend_datainst _ _ _ old fresh
  rcases contents with same | empty
  · exact Or.inl (by simp only [decodeBytes, same])
  · exact Or.inr (by simp only [decodeBytes, empty, List.map_nil])

/-- Actual initialization metadata implies generated store extension. Memory
and table writes preserve limits; segment drops are permitted by the generated
relation. No function body or signature is changed. -/
theorem SegmentObjectMetadata.extends {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (metadata : SegmentObjectMetadata view before after)
    (code : CodeInterpretation)
    (oldWf : wf_store (decodeStore view code before))
    (freshWf : wf_store (decodeStore view code after)) :
    Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have oldFunctions : Forall wf_funcinst (decodeStore view code before).FUNCS := by cases oldWf; assumption
  have oldGlobals : Forall wf_globalinst (decodeStore view code before).GLOBALS := by cases oldWf; assumption
  have oldTables : Forall wf_tableinst (decodeStore view code before).TABLES := by cases oldWf; assumption
  have freshTables : Forall wf_tableinst (decodeStore view code after).TABLES := by cases freshWf; assumption
  have oldMemories : Forall wf_meminst (decodeStore view code before).MEMS := by cases oldWf; assumption
  have freshMemories : Forall wf_meminst (decodeStore view code after).MEMS := by cases freshWf; assumption
  have oldDatas : Forall wf_datainst (decodeStore view code before).DATAS := by cases oldWf; assumption
  have freshDatas : Forall wf_datainst (decodeStore view code after).DATAS := by cases freshWf; assumption
  obtain ⟨globals, _, _, functions, _, _⟩ := Spec.extend_store_objects (Spec.extend_store_refl _ oldWf)
  apply Spec.extend_store_of_objects oldWf freshWf
  · simpa only [decodeStore, metadata.space.globals] using globals
  · apply mapped_objects (decodeMemory view) Extend_meminst before.memories.val after.memories.val metadata.space.memories.ge
    intro index old found
    obtain ⟨fresh, lookup, maximum, length⟩ := metadata.memories index old found
    exact ⟨fresh, lookup, memory_extension view old fresh maximum length
      (oldMemories _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshMemories _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · apply mapped_objects decodeTable Extend_tableinst before.tables.val after.tables.val metadata.space.tables.ge
    intro index old found
    obtain ⟨fresh, lookup, ty, maximum, length⟩ := metadata.tables index old found
    exact ⟨fresh, lookup, table_extension old fresh ty maximum length
      (oldTables _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshTables _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · rw [metadata.space.decoded_functions view code]
    exact functions
  · apply mapped_objects decodeData Extend_datainst before.datas.val after.datas.val metadata.space.datas.ge
    intro index old found
    obtain ⟨fresh, lookup, contents⟩ := metadata.datas index old found
    exact ⟨fresh, lookup, data_extension old fresh contents
      (oldDatas _ (List.mem_map.mpr ⟨old, List.mem_of_getElem? found, rfl⟩))
      (freshDatas _ (List.mem_map.mpr ⟨fresh, List.mem_of_getElem? lookup, rfl⟩))⟩
  · apply mapped_objects decodeElement Extend_eleminst before.elems.val after.elems.val metadata.space.elements.ge
    intro index old found
    obtain ⟨fresh, lookup, ty, contents⟩ := metadata.elements index old found
    exact ⟨fresh, lookup, element_extension old fresh ty contents⟩

/-- Retained or dropped payloads preserve the binary segment length bounds. -/
theorem SegmentObjectMetadata.segment_bounds {M : Type} {view : M → Slice U8}
    {before after : runtime.store.Store M} (metadata : SegmentObjectMetadata view before after)
    (bounds : SegmentBounds before) : SegmentBounds after := by
  constructor
  · intro element member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have oldBound : index < before.elems.length := by simpa only [metadata.space.elements] using bound
    have oldFound : before.elems.val[index]? = some before.elems.val[index] := List.getElem?_eq_getElem oldBound
    obtain ⟨fresh, found, _, contents⟩ := metadata.elements index before.elems.val[index] oldFound
    have same : fresh = element := by
      have read : after.elems.val[index]? = some element := List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
      exact Option.some.inj (found.symm.trans read)
    subst fresh
    have oldLength := bounds.elements before.elems.val[index] (List.mem_of_getElem? oldFound)
    change element.refs.val.length < _
    rcases contents with retained | dropped
    · rw [retained]; exact oldLength
    · simp only [dropped, List.length_nil]; norm_num
  · intro segment member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    have oldBound : index < before.datas.length := by simpa only [metadata.space.datas] using bound
    have oldFound : before.datas.val[index]? = some before.datas.val[index] := List.getElem?_eq_getElem oldBound
    obtain ⟨fresh, found, contents⟩ := metadata.datas index before.datas.val[index] oldFound
    have same : fresh = segment := by
      have read : after.datas.val[index]? = some segment := List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
      exact Option.some.inj (found.symm.trans read)
    subst fresh
    have oldLength := bounds.data before.datas.val[index] (List.mem_of_getElem? oldFound)
    change segment.bytes.val.length < _
    rcases contents with retained | dropped
    · rw [retained]; exact oldLength
    · simp only [dropped, List.length_nil]; norm_num

end Itasca.Runtime.Store
