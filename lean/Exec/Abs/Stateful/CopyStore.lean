import Exec.Abs.Stateful.PayloadTyping
import Exec.Abs.Stateful.ObjectReplacement
import Exec.Abs.Stateful.MemorySize
import Exec.Spec.MemoryCopySnapshot
import Exec.Spec.TableCopySnapshot
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem memoryCopy_preserves (s : store) (f : frame) (address destination source count : Nat)
    (object : meminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object)
    (inside : source+count ≤ object.BYTES.length ∧ destination+count ≤ object.BYTES.length) :
    Extend_store s (Segment.memoryCopy s f destination source count) ∧
      StoreContentsTyped (Segment.memoryCopy s f destination source count) := by
  have typed := contents.memories object (List.mem_of_getElem? found)
  have bytes : Forall wf_byte object.BYTES := by
    have objectWf : wf_meminst object := by cases typed; assumption
    cases objectWf; assumption
  have copied := copyInto_forall wf_byte object.BYTES object.BYTES destination source count bytes bytes inside.1
  have length := Segment.copyInto_length object.BYTES object.BYTES destination source count
  rw [Segment.copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2] at copied length
  obtain ⟨newTyped,objectExtension⟩ := memory_payload_typed typed _ length copied
  have result := memory_replacement_preserves s address object _ wf contents found objectExtension newTyped
  simpa only [Segment.memoryCopy,Segment.withBytes,List.getElem!_eq_getElem?_getD,mapped,found,Option.getD_some] using result

theorem tableCopy_preserves (s : store) (f : frame) (targetTable sourceTable targetAddress sourceAddress destination source count : Nat)
    (targetObject sourceObject : tableinst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (targetMapped : f.MODULE.TABLES[targetTable]? = some targetAddress)
    (sourceMapped : f.MODULE.TABLES[sourceTable]? = some sourceAddress)
    (targetFound : s.TABLES[targetAddress]? = some targetObject) (sourceFound : s.TABLES[sourceAddress]? = some sourceObject)
    (sameType : tableElementType targetObject.TYPE = tableElementType sourceObject.TYPE)
    (inside : source+count ≤ sourceObject.REFS.length ∧ destination+count ≤ targetObject.REFS.length) :
    Extend_store s (Segment.tableCopy s f targetTable sourceTable destination source count) ∧
      StoreContentsTyped (Segment.tableCopy s f targetTable sourceTable destination source count) := by
  have typed := contents.tables targetObject (List.mem_of_getElem? targetFound)
  have old := table_references contents (List.mem_of_getElem? targetFound)
  have fresh := table_references contents (List.mem_of_getElem? sourceFound)
  rw [←sameType] at fresh
  have copied := copyInto_forall _ targetObject.REFS sourceObject.REFS destination source count old fresh inside.1
  have length := Segment.copyInto_length targetObject.REFS sourceObject.REFS destination source count
  rw [Segment.copyInto_eq_setSlice _ _ _ _ _ inside.1 inside.2] at copied length
  obtain ⟨newTyped,objectExtension⟩ := table_payload_typed typed _ length copied
  have result := table_replacement_preserves s targetAddress targetObject _ wf contents targetFound objectExtension newTyped
  simpa only [Segment.tableCopy,Segment.withRefs,List.getElem!_eq_getElem?_getD,targetMapped,sourceMapped,
    targetFound,sourceFound,Option.getD_some] using result
end Itasca.Runtime.Abs.Stateful
