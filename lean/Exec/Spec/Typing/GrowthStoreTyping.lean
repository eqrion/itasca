import Exec.Spec.Typing.GrowthObjectTyping
import Exec.Spec.Typing.StoreMutationTyping

/-! Successful generated memory/table growth preserves genuine store typing
from typed old instances and the independent growth relation. -/

namespace Exec.Spec
open SpecExt

theorem memory_growth_store_typed {s : store} (typed : Store_ok s) (address : Nat) (bound : address<s.MEMS.length)
    (delta : Nat) (next : meminst) (grown : fun_growmemory s.MEMS[address]! delta (some next))
    (postWf : wf_store {s with MEMS := s.MEMS.set address next}) :
    Extend_store s {s with MEMS := s.MEMS.set address next} ∧ Store_ok {s with MEMS := s.MEMS.set address next} := by
  have components := source_store_components typed
  have member : s.MEMS[address]! ∈ s.MEMS := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.memories _ member
  obtain ⟨fresh,objectExtension⟩ := source_growmemory_typed oldTyped grown
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s {s with MEMS := s.MEMS.set address next} :=
    extend_store_set_mem s address next storeWf postWf (fun _ => objectExtension)
  refine ⟨extension,?_⟩
  exact source_store_memory_set typed extension address next rfl (meminst_typing_extend extension fresh)

theorem table_growth_store_typed {s : store} (typed : Store_ok s) (address : Nat) (bound : address<s.TABLES.length)
    (delta : Nat) (value : ref) (valueTyped : Ref_ok s value (sourceTableElementType s.TABLES[address]!.TYPE))
    (next : tableinst) (grown : fun_growtable s.TABLES[address]! delta value (some next))
    (postWf : wf_store {s with TABLES := s.TABLES.set address next}) :
    Extend_store s {s with TABLES := s.TABLES.set address next} ∧ Store_ok {s with TABLES := s.TABLES.set address next} := by
  have components := source_store_components typed
  have member : s.TABLES[address]! ∈ s.TABLES := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.tables _ member
  obtain ⟨fresh,objectExtension⟩ := source_growtable_typed oldTyped valueTyped grown
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s {s with TABLES := s.TABLES.set address next} :=
    extend_store_set_table s address next storeWf postWf (fun _ => objectExtension)
  refine ⟨extension,?_⟩
  exact source_store_table_set typed extension address next rfl (tableinst_typing_extend extension fresh)

end Exec.Spec
