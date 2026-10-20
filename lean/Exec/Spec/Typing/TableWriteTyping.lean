import Exec.Spec.Typing.StoreMutationTyping
/-! Reference replacement preserves the table declaration and typed contents. -/

namespace Exec.Spec
open SpecExt

theorem table_reference_update_typed {s t : store} (extension : Extend_store s t)
    {object : tableinst} {type : tabletype} (typed : Tableinst_ok s object type) (index : Nat) (value : ref)
    (valueTyped : Ref_ok s value (sourceTableElementType type))
    (freshWf : wf_tableinst {object with REFS := object.REFS.set index value}) :
    Tableinst_ok t {object with REFS := object.REFS.set index value} type := by
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsTyped size _ _ typeWf =>
    have members := list_set_members (property := fun reference => Ref_ok t reference type) refs index value (ref_ok_extend extension valueTyped)
    have freshRefs : Forall (fun reference => Ref_ok t reference type) (refs.set index value) := by
      intro reference member
      rcases members reference member with old | fresh
      · exact ref_ok_extend extension (refsTyped reference old)
      · exact fresh
    exact .mk_Tableinst_ok _ _ _ _ _ typeOk freshRefs (by simpa only [List.length_set] using size)
      (extend_store_wf extension).2 freshWf typeWf

theorem table_reference_update_extends {s : store} {object : tableinst} {type : tabletype}
    (typed : Tableinst_ok s object type) (index : Nat) (value : ref)
    (freshWf : wf_tableinst {object with REFS := object.REFS.set index value}) :
    Extend_tableinst object {object with REFS := object.REFS.set index value} := by
  cases typed with
  | mk_Tableinst_ok count maximum type refs _ _ _ _ objectWf _ =>
    exact .mk_Extend_tableinst count maximum type refs count (refs.set index value) (Nat.le_refl _)
      (by simp only [List.length_set]; exact Nat.le_refl _) objectWf freshWf

def sourceTableUpdate (s : store) (address position : Nat) (value : ref) : store :=
  {s with TABLES := s.TABLES.set address {s.TABLES[address]! with REFS := s.TABLES[address]!.REFS.set position value}}

theorem store_table_wf {s : store} (typed : wf_store s) : Forall wf_tableinst s.TABLES := by cases typed; assumption

theorem table_update_store_typed {s : store} (typed : Store_ok s) (address : Nat) (bound : address<s.TABLES.length)
    (position : Nat) (value : ref) (valueTyped : Ref_ok s value (sourceTableElementType s.TABLES[address]!.TYPE))
    (postWf : wf_store (sourceTableUpdate s address position value)) :
    Extend_store s (sourceTableUpdate s address position value) ∧ Store_ok (sourceTableUpdate s address position value) := by
  have components := source_store_components typed
  have member : s.TABLES[address]! ∈ s.TABLES := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.tables _ member
  have freshWf : wf_tableinst {s.TABLES[address]! with REFS := s.TABLES[address]!.REFS.set position value} := by
    apply store_table_wf postWf
    exact List.mem_set bound _
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s (sourceTableUpdate s address position value) :=
    extend_store_set_table s address _ storeWf postWf (fun _ => table_reference_update_extends oldTyped position value freshWf)
  refine ⟨extension,?_⟩
  apply source_store_table_set typed extension address _ rfl
  exact table_reference_update_typed extension oldTyped position value valueTyped freshWf

end Exec.Spec
