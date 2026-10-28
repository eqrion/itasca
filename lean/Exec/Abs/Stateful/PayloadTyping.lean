import Exec.Abs.Stateful.TableTyping
import Exec.Abs.Core.MemoryMutation
import Exec.Spec.SegmentCopy
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem copyInto_forall {T : Type} [Inhabited T] (property : T → Prop)
    (before source : List T) (destination offset count : Nat)
    (old : Forall property before) (values : Forall property source)
    (inside : offset+count ≤ source.length) :
    Forall property (Segment.copyInto before source destination offset count) := by
  induction count generalizing before destination offset with
  | zero => exact old
  | succ count ih =>
    apply ih (before.set destination source[offset]!) (destination+1) (offset+1) _ (by omega)
    intro value member
    rcases List.mem_or_eq_of_mem_set member with member | rfl
    · exact old value member
    · exact values source[offset]! (by rw [getElem!_pos source offset (by omega)]; exact List.getElem_mem (by omega))

theorem table_payload_typed {s : store} {object : tableinst} (typed : Tableinst_ok s object object.TYPE)
    (values : List ref) (length : values.length = object.REFS.length)
    (refs : Forall (fun value => Ref_ok s value (tableElementType object.TYPE)) values) :
    Tableinst_ok s {object with REFS := values} object.TYPE ∧
      Extend_tableinst object {object with REFS := values} := by
  cases typed with
  | mk_Tableinst_ok count maximum type old typeOk oldRefs oldLength storeWf objectWf typeWf =>
    refine ⟨.mk_Tableinst_ok _ _ _ _ _ typeOk refs ?_ storeWf (.tableinst_case_ _ _ typeWf) typeWf,?_⟩
    · exact length.trans oldLength
    · exact extend_table_contents count count maximum type old values (by rfl) (by simpa only using length.ge) objectWf (.tableinst_case_ _ _ typeWf)

theorem memory_payload_typed {s : store} {object : meminst} (typed : Meminst_ok s object object.TYPE)
    (bytes : List byte) (length : bytes.length = object.BYTES.length) (values : Forall wf_byte bytes) :
    Meminst_ok s {object with BYTES := bytes} object.TYPE ∧
      Extend_meminst object {object with BYTES := bytes} := by
  cases typed with
  | mk_Meminst_ok count maximum old typeOk oldLength storeWf objectWf typeWf =>
    refine ⟨.mk_Meminst_ok _ _ _ _ typeOk ?_ storeWf (.meminst_case_ _ _ typeWf values) typeWf,?_⟩
    · exact length.trans oldLength
    · exact extend_mem_contents count count maximum old bytes (by rfl) (by simpa only using length.ge) objectWf (.meminst_case_ _ _ typeWf values)
end Itasca.Runtime.Abs.Stateful
