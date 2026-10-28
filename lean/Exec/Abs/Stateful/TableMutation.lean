import Exec.Abs.Stateful.TableTyping
import Exec.Abs.Core.ContentExtension
import Exec.Spec.TableInitSource
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem tableWrite_as_set (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (mapped : f.MODULE.TABLES[index]? = some address)
    (found : s.TABLES[address]? = some object) :
    Segment.tableWrite s f index position value =
      {s with TABLES := s.TABLES.set address {object with REFS := object.REFS.modify position (fun _ => value)}} := by
  simp only [Segment.tableWrite,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem tableWrite_extends (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object) :
    Extend_store s (Segment.tableWrite s f index position value) := by
  have fresh := Segment.tableWrite_wf s f index position value wf
  rw [tableWrite_as_set s f index address position object value mapped found] at fresh ⊢
  apply extend_store_set_table s address _ wf fresh
  intro bound
  simp only [List.getElem!_eq_getElem?_getD,found,Option.getD_some]
  have typed := contents.tables object (List.mem_of_getElem? found)
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ oldWf typeWf =>
    exact extend_table_contents count count maximum type refs (refs.modify position (fun _ => value))
      (by rfl) (by simp) oldWf (.tableinst_case_ _ _ typeWf)

theorem tableWrite_contents (s : store) (f : frame) (index address position : Nat)
    (object : tableinst) (value : ref) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE)) :
    StoreContentsTyped (Segment.tableWrite s f index position value) := by
  have extension := tableWrite_extends s f index address position object value wf contents mapped found
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact fun item member => globalinst_typed_extend extension (contents.globals item member)
  · intro item member
    have objects := congrArg store.TABLES (tableWrite_as_set s f index address position object value mapped found)
    rw [objects] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact tableinst_typed_extend extension (contents.tables item member)
    · have typed := contents.tables object (List.mem_of_getElem? found)
      cases typed with
      | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ oldWf typeWf =>
        apply Tableinst_ok.mk_Tableinst_ok _ count maximum type (refs.modify position (fun _ => value)) typeOk
        · apply Segment.forall_modify
          · exact fun reference member => ref_ok_extend extension (refsOk reference member)
          · intro reference _
            exact ref_ok_extend extension valueTyped
        · simpa only [List.length_modify] using length
        · exact (extend_store_wf extension).2
        · exact .tableinst_case_ _ _ typeWf
        · exact typeWf
  · exact fun item member => meminst_typed_extend extension (contents.memories item member)
  · exact fun item member => eleminst_ok_extend extension (extend_elem_refl item) (contents.elements item member)
  · intro item member
    have typed := contents.data item member
    have itemWf : wf_datainst item := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl item itemWf) typed
end Itasca.Runtime.Abs.Stateful
