import Exec.Store.Invariant.BindingTyping
import Exec.Store.Initialization.ElementTypes
namespace Exec.Store
open Aeneas Aeneas.Std Itasca

theorem GlobalTypeMap.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : GlobalTypeMap store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.GLOBAL address) (.GLOBAL ty))
      (addresses.map (fun address => address.index.val)) (types.map Translate.globalType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_global_typed view code store wellformed _ _ linked) ih

theorem TableBindings.source {M : Type} {store : runtime.store.Store M} {types addresses}
    (mapping : TableBindings store types addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.TABLE address) (.TABLE ty))
      (addresses.map (fun address => address.index.val)) (types.map EnvTranslation.tableType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_table_typed view code store wellformed shape _ _ linked) ih

theorem MemoryBindings.source {M : Type} {view : M → Slice U8} {store : runtime.store.Store M} {types addresses}
    (mapping : MemoryBindings view store types addresses) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store) :
    List.Forall₂ (fun address ty => Externaddr_ok (decodeStore view code store) (.MEM address) (.MEM ty))
      (addresses.map (fun address => address.index.val)) (types.map EnvTranslation.memType) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih => exact .cons (imported_memory_typed view code store wellformed shape _ _ linked) ih

theorem ElementTypeMap.source {M : Type} {store : runtime.store.Store M} {entries addresses}
    (mapping : ElementTypeMap store entries addresses) (view : M → Slice U8) (code : CodeInterpretation)
    (wellformed : wf_store (decodeStore view code store)) (shape : Shape view store)
    (bounds : SegmentBounds store) :
    List.Forall₂ (fun address ty => ∃ element,
      (decodeStore view code store).ELEMS[address]? = some element ∧
      Eleminst_ok (decodeStore view code store) element ty)
      (addresses.map UScalar.val) (entries.map (fun entry => Translate.referenceType entry.elem)) := by
  induction mapping with
  | nil => exact .nil
  | cons linked rest ih =>
    obtain ⟨segment, found, typed⟩ := linked
    apply List.Forall₂.cons ?_ ih
    refine ⟨decodeElement segment, ?_, ?_⟩
    · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
    · have checked := decodeElement_typed view code store wellformed segment
        (shape.elements segment (List.mem_of_getElem? found)) (bounds.elements segment (List.mem_of_getElem? found))
      simpa only [decodeElement, typed, decodeElemType_source] using checked

theorem data_addresses_typed {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (addresses : List Usize)
    (wellformed : wf_store (decodeStore view code store)) (bounds : SegmentBounds store)
    (issued : ∀ address ∈ addresses, address.val < store.datas.length) :
    List.Forall₂ (fun address ty => ∃ segment,
      (decodeStore view code store).DATAS[address]? = some segment ∧
      Datainst_ok (decodeStore view code store) segment ty)
      (addresses.map UScalar.val) (List.replicate addresses.length datatype.OK) := by
  induction addresses with
  | nil => exact .nil
  | cons address rest ih =>
    have bound := issued address (by simp)
    let segment := store.datas.val[address.val]
    have found : store.datas.val[address.val]? = some segment := List.getElem?_eq_getElem bound
    apply List.Forall₂.cons
    · refine ⟨decodeData segment, ?_, ?_⟩
      · simp only [decodeStore, List.getElem?_map, found, Option.map_some]
      · exact decodeData_typed _ wellformed segment (bounds.data segment (List.mem_of_getElem? found))
    · exact ih (fun value member => issued value (by simp [member]))

end Exec.Store
