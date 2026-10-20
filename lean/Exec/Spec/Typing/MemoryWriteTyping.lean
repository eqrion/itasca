import Exec.Spec.Typing.StoreMutationTyping
/-! Generated clamped byte splices preserve exact memory size and genuine
source store typing. -/

namespace Exec.Spec
open SpecExt

theorem source_splice_length {A : Type} (before replacement : List A) (position : Nat) :
    (splice before replacement position).length=before.length := by
  let start := Nat.min position before.length
  let count := Nat.min replacement.length (before.length-start)
  have startBound : start ≤ before.length := Nat.min_le_right _ _
  have countBound : count ≤ before.length-start := Nat.min_le_right _ _
  have payloadBound : count ≤ replacement.length := Nat.min_le_left _ _
  change (before.take start++replacement.take count++before.drop (start+count)).length=before.length
  simp only [List.length_append,List.length_take,List.length_drop,Nat.min_eq_left startBound,Nat.min_eq_left payloadBound]
  omega

theorem memory_bytes_update_typed {s t : store} (extension : Extend_store s t)
    {object : meminst} {type : memtype} (typed : Meminst_ok s object type) (bytes : List byte)
    (length : bytes.length=object.BYTES.length) (freshWf : wf_meminst {object with BYTES := bytes}) :
    Meminst_ok t {object with BYTES := bytes} type := by
  cases typed with
  | mk_Meminst_ok count maximum oldBytes typeOk size _ _ typeWf =>
    exact .mk_Meminst_ok _ _ _ _ typeOk (length.trans size) (extend_store_wf extension).2 freshWf typeWf

theorem memory_bytes_update_extends {s : store} {object : meminst} {type : memtype}
    (typed : Meminst_ok s object type) (bytes : List byte) (length : bytes.length=object.BYTES.length)
    (freshWf : wf_meminst {object with BYTES := bytes}) : Extend_meminst object {object with BYTES := bytes} := by
  cases typed with
  | mk_Meminst_ok count maximum oldBytes typeOk size _ objectWf typeWf =>
    exact .mk_Extend_meminst count maximum oldBytes count bytes (Nat.le_refl count)
      (by simpa only using Nat.le_of_eq length.symm) objectWf freshWf

def sourceMemoryUpdate (s : store) (index position : Nat) (replacement : List byte) : store :=
  {s with MEMS := s.MEMS.set index {s.MEMS[index]! with
    BYTES := splice s.MEMS[index]!.BYTES replacement position}}

theorem store_memory_wf {s : store} (typed : wf_store s) : Forall wf_meminst s.MEMS := by cases typed; assumption

theorem memory_update_store_typed {s : store} (typed : Store_ok s) (index : Nat) (bound : index<s.MEMS.length)
    (position : Nat) (replacement : List byte)
    (postWf : wf_store (sourceMemoryUpdate s index position replacement)) :
    Extend_store s (sourceMemoryUpdate s index position replacement) ∧
      Store_ok (sourceMemoryUpdate s index position replacement) := by
  have components := source_store_components typed
  have member : s.MEMS[index]! ∈ s.MEMS := by
    simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using List.getElem_mem bound
  have oldTyped := components.memories _ member
  have length := source_splice_length s.MEMS[index]!.BYTES replacement position
  have freshWf : wf_meminst {s.MEMS[index]! with
      BYTES := splice s.MEMS[index]!.BYTES replacement position} := by
    apply store_memory_wf postWf
    exact List.mem_set bound _
  have storeWf : wf_store s := by cases typed; assumption
  have extension : Extend_store s (sourceMemoryUpdate s index position replacement) :=
    extend_store_set_mem s index _ storeWf postWf (fun _ => memory_bytes_update_extends oldTyped _ length freshWf)
  refine ⟨extension,?_⟩
  apply source_store_memory_set typed extension index _ rfl
  exact memory_bytes_update_typed extension oldTyped _ length freshWf

end Exec.Spec
