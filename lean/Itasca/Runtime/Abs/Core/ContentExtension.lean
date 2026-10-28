import Itasca.Runtime.Abs.Core.Typing

namespace Itasca.Runtime.Abs
open Itasca.Runtime.Spec

theorem globalinst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Globalinst_ok before object ty) : Globalinst_ok after object ty := by
  cases typed with
  | mk_Globalinst_ok mutable type value typeOk valueOk _ wf =>
    exact .mk_Globalinst_ok _ _ _ _ typeOk (val_typed_extend extension valueOk)
      (extend_store_wf extension).2 wf

theorem tableinst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Tableinst_ok before object ty) : Tableinst_ok after object ty := by
  cases typed with
  | mk_Tableinst_ok count maximum type refs typeOk refsOk length _ wf typeWf =>
    exact .mk_Tableinst_ok _ _ _ _ _ typeOk
      (fun value member => ref_ok_extend extension (refsOk value member)) length
      (extend_store_wf extension).2 wf typeWf

theorem meminst_typed_extend {before after : store} (extension : Extend_store before after)
    {object ty} (typed : Meminst_ok before object ty) : Meminst_ok after object ty := by
  cases typed with
  | mk_Meminst_ok count maximum bytes typeOk length _ wf typeWf =>
    exact .mk_Meminst_ok _ _ _ _ typeOk length (extend_store_wf extension).2 wf typeWf

/-- The unchanged payloads remain typed after a store mutation; the replacement
itself must be checked at its declared type. -/
theorem StoreContentsTyped.global_replacement {before after : store}
    (contents : StoreContentsTyped before) (extension : Extend_store before after)
    (address : Nat) (object : globalinst)
    (globals : after.GLOBALS = before.GLOBALS.set address object)
    (tables : after.TABLES = before.TABLES) (memories : after.MEMS = before.MEMS)
    (elements : after.ELEMS = before.ELEMS) (data : after.DATAS = before.DATAS)
    (replacement : Globalinst_ok after object object.TYPE) : StoreContentsTyped after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [globals]
    have old : ∀ global ∈ before.GLOBALS, Globalinst_ok after global global.TYPE :=
      fun global member => globalinst_typed_extend extension (contents.globals global member)
    intro global member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact old global member
    · exact replacement
  · intro table member
    rw [tables] at member
    exact tableinst_typed_extend extension (contents.tables table member)
  · intro memory member
    rw [memories] at member
    exact meminst_typed_extend extension (contents.memories memory member)
  · intro element member
    rw [elements] at member
    exact eleminst_ok_extend extension (extend_elem_refl element) (contents.elements element member)
  · intro entry member
    rw [data] at member
    have typed := contents.data entry member
    have wf : wf_datainst entry := by cases typed; assumption
    exact datainst_ok_extend extension (extend_data_refl entry wf) typed

end Itasca.Runtime.Abs
