import Itasca.Runtime.SourceMachine.Stateful.PayloadTyping
import Itasca.Runtime.SourceMachine.Stateful.ObjectReplacement
import Itasca.Runtime.SourceMachine.Stateful.MemorySize
import Itasca.Runtime.Spec.MemoryInit
import Itasca.Runtime.Spec.TableInit
namespace Itasca.Runtime.SourceMachine.Stateful
open SpecExt Itasca.Runtime.Spec

theorem memory_byte_length_bound {s : store} (contents : StoreContentsTyped s) {object : meminst}
    (member : object ∈ s.MEMS) : object.BYTES.length ≤ 2^32 := by
  have pages := memory_pages_bound contents member
  have aligned := memory_pages_aligned contents member
  have division := Nat.mod_add_div object.BYTES.length 65536
  omega

theorem data_bytes_typed {s : store} {object : datainst} (typed : Datainst_ok s object .OK) :
    object.BYTES.length < 2^32 ∧ Forall wf_byte object.BYTES := by
  cases typed with
  | mk_Datainst_ok bytes bound wf objectWf =>
    exact ⟨bound,by cases objectWf; assumption⟩

theorem element_refs_typed {s : store} {object : eleminst} {type : reftype} (typed : Eleminst_ok s object type) :
    object.TYPE = type ∧ object.REFS.length < 2^32 ∧ Forall (fun value => Ref_ok s value type) object.REFS := by
  cases typed with
  | mk_Eleminst_ok type refs refsOk bound wf => exact ⟨rfl,bound,refsOk⟩

theorem memory_init_preserves (s : store) (f : frame) (address dataIndex dataAddress destination source count : Nat)
    (object : meminst) (data : datainst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (dataMapped : f.MODULE.DATAS[dataIndex]? = some dataAddress) (dataFound : s.DATAS[dataAddress]? = some data)
    (inside : source+count ≤ data.BYTES.length ∧ destination+count ≤ object.BYTES.length) :
    Extend_store s (Segment.memoryInit s f dataIndex destination source count) ∧
      StoreContentsTyped (Segment.memoryInit s f dataIndex destination source count) ∧
      (Segment.memoryInit s f dataIndex destination source count).FUNCS = s.FUNCS := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have bytes : Forall wf_byte object.BYTES := by
    have objectWf : wf_meminst object := by cases typed; assumption
    cases objectWf; assumption
  obtain ⟨dataBound,dataBytes⟩ := data_bytes_typed (contents.data data (List.mem_of_getElem? dataFound))
  have copied := copy_into_forall wf_byte object.BYTES data.BYTES destination source count bytes dataBytes inside.1
  have length := Segment.copy_into_length object.BYTES data.BYTES destination source count
  obtain ⟨newTyped,objectExtension⟩ := memory_payload_typed typed _ length copied
  have result := memory_replacement_preserves s address object _ wf contents found objectExtension newTyped
  have memoryEq : fun_mem ⟨s,f⟩ (.mk_uN 0) = object := by simp [fun_mem,proj_uN_0,List.getElem!_eq_getElem?_getD,mapped,found]
  have dataEq : fun_data ⟨s,f⟩ (.mk_uN dataIndex) = data := by simp [fun_data,proj_uN_0,List.getElem!_eq_getElem?_getD,dataMapped,dataFound]
  have memoryBound := memory_byte_length_bound contents (List.mem_of_getElem? found)
  have addressBound : f.MODULE.MEMS[0]! < s.MEMS.length := by
    simpa only [List.getElem!_eq_getElem?_getD,mapped,Option.getD_some] using (List.getElem?_eq_some_iff.mp found).1
  have final := Segment.memory_init_eq s f dataIndex destination source count addressBound
    (by simpa only [memoryEq] using memoryBound) (by simpa only [dataEq] using dataBound.le)
    (by simpa only [memoryEq,dataEq] using inside)
  simp only [dataEq,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found,Option.map_some] at final
  rw [final]
  exact ⟨result.1,result.2,rfl⟩

theorem table_init_preserves (s : store) (f : frame) (tableIndex elementIndex tableAddress elementAddress destination source count : Nat)
    (object : tableinst) (element : eleminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[tableIndex]? = some tableAddress) (found : s.TABLES[tableAddress]? = some object)
    (elementMapped : f.MODULE.ELEMS[elementIndex]? = some elementAddress) (elementFound : s.ELEMS[elementAddress]? = some element)
    (sameType : tableElementType object.TYPE = element.TYPE)
    (inside : source+count ≤ element.REFS.length ∧ destination+count ≤ object.REFS.length) :
    Extend_store s (Segment.tableInit s f tableIndex elementIndex destination source count) ∧
      StoreContentsTyped (Segment.tableInit s f tableIndex elementIndex destination source count) ∧
      (Segment.tableInit s f tableIndex elementIndex destination source count).FUNCS = s.FUNCS := by
  have typed := contents.tables object (List.mem_of_getElem? found)
  have refs := table_references contents (List.mem_of_getElem? found)
  obtain ⟨_,elementBound,elementRefs⟩ := element_refs_typed (contents.elements element (List.mem_of_getElem? elementFound))
  rw [←sameType] at elementRefs
  have copied := copy_into_forall _ object.REFS element.REFS destination source count refs elementRefs inside.1
  have length := Segment.copy_into_length object.REFS element.REFS destination source count
  obtain ⟨newTyped,objectExtension⟩ := table_payload_typed typed _ length copied
  have result := table_replacement_preserves s tableAddress object _ wf contents found objectExtension newTyped
  have elementEq : fun_elem ⟨s,f⟩ (.mk_uN elementIndex) = element := by simp [fun_elem,proj_uN_0,List.getElem!_eq_getElem?_getD,elementMapped,elementFound]
  have final := Segment.table_init_eq s f tableIndex elementIndex destination source count
  simp only [elementEq,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some,List.modify_eq_set_getElem?,found,Option.map_some] at final
  rw [final]
  exact ⟨result.1,result.2,rfl⟩
end Itasca.Runtime.SourceMachine.Stateful
