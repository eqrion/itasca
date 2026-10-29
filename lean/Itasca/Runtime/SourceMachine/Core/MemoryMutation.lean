import Itasca.Runtime.SourceMachine.Core.ContentExtension
import Itasca.Runtime.SourceMachine.Memory.Semantics

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem memoryPayloadWrite_as_set (s : store) (f : frame) (address start : Nat)
    (object : meminst) (payload : List byte) (mapped : f.MODULE.MEMS[0]? = some address)
    (found : s.MEMS[address]? = some object) :
    Spec.memoryPayloadWrite s f start payload =
      {s with MEMS := s.MEMS.set address {object with BYTES := splice object.BYTES payload start}} := by
  simp only [Spec.memoryPayloadWrite,List.getElem!_eq_getElem?_getD,mapped,Option.getD_some]
  rw [List.modify_eq_set_getElem?]
  simp only [found]
  rfl

theorem splice_length {T : Type} (bytes payload : List T) (start : Nat) :
    (splice bytes payload start).length = bytes.length := by
  simp only [splice,List.length_append,List.length_take,List.length_drop]
  omega

theorem splice_wf (bytes payload : List byte) (start : Nat)
    (old : Forall wf_byte bytes) (fresh : Forall wf_byte payload) :
    Forall wf_byte (splice bytes payload start) := by
  intro byte member
  simp only [splice,List.mem_append] at member
  rcases member with (first | middle) | last
  · exact old byte (List.mem_of_mem_take first)
  · exact fresh byte (List.mem_of_mem_take middle)
  · exact old byte (List.mem_of_mem_drop last)

theorem memoryPayloadWrite_extends (s : store) (f : frame) (address start : Nat)
    (object : meminst) (payload : List byte) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (payloadWf : Forall wf_byte payload) : Extend_store s (Spec.memoryPayloadWrite s f start payload) := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have freshWf := memoryPayloadWrite_wf s f start payload wf payloadWf
  rw [memoryPayloadWrite_as_set s f address start object payload mapped found] at freshWf ⊢
  apply extend_store_set_mem _ _ _ wf freshWf
  intro bound
  have atAddress : s.MEMS[address]! = object := by simp [List.getElem!_eq_getElem?_getD,found]
  rw [atAddress]
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length storeWf objectWf typeWf =>
    have byteWf : Forall wf_byte bytes := by cases objectWf; assumption
    exact extend_mem_contents count count maximum bytes (splice bytes payload start)
      (by omega) (by rw [splice_length]) objectWf
      (.meminst_case_ _ _ typeWf (splice_wf bytes payload start byteWf payloadWf))

theorem StoreContentsTyped.memory_replacement {before after : store}
    (contents : StoreContentsTyped before) (extension : Extend_store before after)
    (address : Nat) (object : meminst)
    (memories : after.MEMS = before.MEMS.set address object)
    (globals : after.GLOBALS = before.GLOBALS) (tables : after.TABLES = before.TABLES)
    (elements : after.ELEMS = before.ELEMS) (data : after.DATAS = before.DATAS)
    (replacement : Meminst_ok after object object.TYPE) : StoreContentsTyped after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro global member
    rw [globals] at member
    exact globalinst_typed_extend extension (contents.globals global member)
  · intro table member
    rw [tables] at member
    exact tableinst_typed_extend extension (contents.tables table member)
  · intro memory member
    rw [memories] at member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact meminst_typed_extend extension (contents.memories memory member)
    · exact replacement
  · intro element member
    rw [elements] at member
    exact eleminst_ok_extend extension (extend_elem_refl element) (contents.elements element member)
  · intro entry member
    rw [data] at member
    have typed := contents.data entry member
    have wf : wf_datainst entry := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl entry wf) typed

theorem StoreContentsTyped.memory_write {s : store} (contents : StoreContentsTyped s)
    (wf : wf_store s) (f : frame) (address start : Nat) (object : meminst) (payload : List byte)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (payloadWf : Forall wf_byte payload) : StoreContentsTyped (Spec.memoryPayloadWrite s f start payload) := by
  have extension := memoryPayloadWrite_extends s f address start object payload wf contents mapped found payloadWf
  have freshWf := (extend_store_wf extension).2
  have typed := contents.memories object (List.mem_of_getElem? found)
  have objectFresh : Meminst_ok (Spec.memoryPayloadWrite s f start payload)
      {object with BYTES := splice object.BYTES payload start} object.TYPE := by
    cases typed with
    | mk_Meminst_ok count maximum bytes typeOk length storeWf objectWf typeWf =>
      have byteWf : Forall wf_byte bytes := by cases objectWf; assumption
      exact .mk_Meminst_ok _ _ _ _ typeOk (by simpa only [splice_length] using length) freshWf
        (.meminst_case_ _ _ typeWf (splice_wf bytes payload start byteWf payloadWf)) typeWf
  exact contents.memory_replacement extension address {object with BYTES := splice object.BYTES payload start}
    (congrArg store.MEMS (memoryPayloadWrite_as_set s f address start object payload mapped found))
    rfl rfl rfl rfl objectFresh

end Itasca.Runtime.Abs
