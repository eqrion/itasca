import Exec.Abs.Core.ContentExtension
import Exec.Spec.SegmentDrops
import Exec.Spec.TableInitSource
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem droppedElementStore_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedElementStore s f index) := by
  cases s
  cases wf
  constructor <;> assumption

theorem droppedDataStore_wf (s : store) (f : frame) (index : Nat)
    (wf : wf_store s) : wf_store (droppedDataStore s f index) := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases wf with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  exact .store_case_ _ _ _ _ _ _ hf hg ht hm
    (Segment.forall_modify _ _ _ _ hd (fun entry _ => .datainst_case_ _ (by simp [Forall])))

theorem droppedElementStore_as_set (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (mapped : f.MODULE.ELEMS[index]? = some address)
    (found : s.ELEMS[address]? = some object) :
    droppedElementStore s f index = {s with ELEMS := s.ELEMS.set address {object with REFS := []}} := by
  simp only [droppedElementStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem droppedDataStore_as_set (s : store) (f : frame) (index address : Nat)
    (object : datainst) (mapped : f.MODULE.DATAS[index]? = some address)
    (found : s.DATAS[address]? = some object) :
    droppedDataStore s f index = {s with DATAS := s.DATAS.set address {object with BYTES := []}} := by
  simp only [droppedDataStore,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem droppedElementStore_extends (s : store) (f : frame) (index address : Nat)
    (object : eleminst) (wf : wf_store s)
    (mapped : f.MODULE.ELEMS[index]? = some address) (found : s.ELEMS[address]? = some object) :
    Extend_store s (droppedElementStore s f index) := by
  have fresh := droppedElementStore_wf s f index wf
  rw [droppedElementStore_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_elem s address _ wf fresh
  intro bound
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_eleminst _ _ _ (Or.inr rfl)

theorem droppedDataStore_extends (s : store) (f : frame) (index address : Nat)
    (object : datainst) (wf : wf_store s)
    (mapped : f.MODULE.DATAS[index]? = some address) (found : s.DATAS[address]? = some object) :
    Extend_store s (droppedDataStore s f index) := by
  have fresh := droppedDataStore_wf s f index wf
  rw [droppedDataStore_as_set s f index address object mapped found] at fresh ⊢
  apply extend_store_set_data s address _ wf fresh
  intro bound
  have old : wf_datainst object := by cases wf; apply_assumption; exact List.mem_of_getElem? found
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  cases object
  exact .mk_Extend_datainst _ _ (Or.inr rfl) old (.datainst_case_ _ (by simp [Forall]))

theorem droppedElementStore_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedElementStore s f index)) :
    StoreContentsTyped (droppedElementStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · change Forall (fun object => Eleminst_ok _ object object.TYPE) (s.ELEMS.modify _ _)
    apply Segment.forall_modify
    · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
    · intro object typed
      cases typed with
      | mk_Eleminst_ok type refs refsOk length wf =>
        exact .mk_Eleminst_ok _ _ [] (by simp [Forall]) (by norm_num) wf
  · intro object member
    have typed := contents.data object member
    have wf : wf_datainst object := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl object wf) typed

theorem droppedDataStore_contents (s : store) (f : frame) (index : Nat)
    (contents : StoreContentsTyped s) (extension : Extend_store s (droppedDataStore s f index)) :
    StoreContentsTyped (droppedDataStore s f index) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun object member => globalinst_typed_extend extension (contents.globals object member)
  · exact fun object member => tableinst_typed_extend extension (contents.tables object member)
  · exact fun object member => meminst_typed_extend extension (contents.memories object member)
  · exact fun object member => eleminst_ok_extend extension (extend_elem_refl object) (contents.elements object member)
  · change Forall (fun object => Datainst_ok _ object .OK) (s.DATAS.modify _ _)
    apply Segment.forall_modify
    · intro object member
      have typed := contents.data object member
      have wf : wf_datainst object := by cases typed; assumption
      exact datainst_ok_extend extension (extend_data_refl object wf) typed
    · intro object typed
      exact .mk_Datainst_ok _ [] (by norm_num) (extend_store_wf extension).2 (.datainst_case_ _ (by simp [Forall]))
end Exec.Abs.Stateful
