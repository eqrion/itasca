import Exec.Abs.Core.MemoryMutation
import Exec.Abs.Stateful.TableTyping
namespace Exec.Abs.Stateful
open SpecExt Exec.Spec

theorem wf_store_table_set (s : store) (index : Nat) (value : tableinst)
    (old : wf_store s) (fresh : wf_tableinst value) : wf_store {s with TABLES := s.TABLES.set index value} := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases old with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  refine .store_case_ _ _ _ _ _ _ hf hg ?_ hm hd
  intro table member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact ht table member
  · exact fresh

theorem wf_store_memory_set (s : store) (index : Nat) (value : meminst)
    (old : wf_store s) (fresh : wf_meminst value) : wf_store {s with MEMS := s.MEMS.set index value} := by
  cases s with | MKstore funcs globals tables memories elements data =>
  cases old with | store_case_ _ _ _ _ _ _ hf hg ht hm hd =>
  refine .store_case_ _ _ _ _ _ _ hf hg ht ?_ hd
  intro memory member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact hm memory member
  · exact fresh

theorem table_replacement_preserves (s : store) (index : Nat) (old fresh : tableinst)
    (wf : wf_store s) (contents : StoreContentsTyped s) (found : s.TABLES[index]? = some old)
    (extension : Extend_tableinst old fresh) (typed : Tableinst_ok s fresh fresh.TYPE) :
    Extend_store s {s with TABLES := s.TABLES.set index fresh} ∧
      StoreContentsTyped {s with TABLES := s.TABLES.set index fresh} := by
  have objectWf : wf_tableinst fresh := by cases typed; assumption
  have freshWf := wf_store_table_set s index fresh wf objectWf
  have extended : Extend_store s {s with TABLES := s.TABLES.set index fresh} := by
    apply extend_store_set_table _ _ _ wf freshWf
    intro bound
    simpa only [List.getElem!_eq_getElem?_getD,found,Option.getD_some] using extension
  refine ⟨extended,?_,?_,?_,?_,?_⟩
  · exact fun item member => globalinst_typed_extend extended (contents.globals item member)
  · intro item member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact tableinst_typed_extend extended (contents.tables item member)
    · exact tableinst_typed_extend extended typed
  · exact fun item member => meminst_typed_extend extended (contents.memories item member)
  · exact fun item member => eleminst_ok_extend extended (extend_elem_refl item) (contents.elements item member)
  · intro item member
    have entryTyped := contents.data item member
    have entryWf : wf_datainst item := by cases entryTyped; assumption
    exact datainst_ok_extend extended (extend_data_refl item entryWf) entryTyped

theorem memory_replacement_preserves (s : store) (index : Nat) (old fresh : meminst)
    (wf : wf_store s) (contents : StoreContentsTyped s) (found : s.MEMS[index]? = some old)
    (extension : Extend_meminst old fresh) (typed : Meminst_ok s fresh fresh.TYPE) :
    Extend_store s {s with MEMS := s.MEMS.set index fresh} ∧
      StoreContentsTyped {s with MEMS := s.MEMS.set index fresh} := by
  have objectWf : wf_meminst fresh := by cases typed; assumption
  have freshWf := wf_store_memory_set s index fresh wf objectWf
  have extended : Extend_store s {s with MEMS := s.MEMS.set index fresh} := by
    apply extend_store_set_mem _ _ _ wf freshWf
    intro bound
    simpa only [List.getElem!_eq_getElem?_getD,found,Option.getD_some] using extension
  refine ⟨extended,contents.memory_replacement extended index fresh rfl rfl rfl rfl rfl ?_⟩
  exact meminst_typed_extend extended typed
end Exec.Abs.Stateful
