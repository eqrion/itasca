import Itasca.Runtime.Abs.Stateful.TableMutation
import Itasca.Runtime.Abs.Core.MemoryMutation
import Itasca.Runtime.Spec.TableFillSource
import Itasca.Runtime.Spec.MemoryFillSource
namespace Itasca.Runtime.Abs.Stateful
open SpecExt Itasca.Runtime.Spec

theorem tableFill_preserves (s : store) (f : frame) (index address destination : Nat)
    (object : tableinst) (value : ref) (count : Nat) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.TABLES[index]? = some address) (found : s.TABLES[address]? = some object)
    (valueTyped : Ref_ok s value (tableElementType object.TYPE)) :
    Extend_store s (Segment.tableFill s f index destination value count) ∧
      StoreContentsTyped (Segment.tableFill s f index destination value count) ∧
      (Segment.tableFill s f index destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s object destination with
  | zero => exact ⟨extend_store_refl s wf,contents,rfl⟩
  | succ count ih =>
    have extension := tableWrite_extends s f index address destination object value wf contents mapped found
    have fresh := tableWrite_contents s f index address destination object value wf contents mapped found valueTyped
    have lookup : (Segment.tableWrite s f index destination value).TABLES[address]? =
        some {object with REFS := object.REFS.modify destination (fun _ => value)} := by
      rw [tableWrite_as_set s f index address destination object value mapped found]
      simp only [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
    have valueFresh := ref_ok_extend extension valueTyped
    obtain ⟨later,typed,functions⟩ := ih (Segment.tableWrite s f index destination value)
      (destination+1) {object with REFS := object.REFS.modify destination (fun _ => value)}
      (extend_store_wf extension).2 fresh lookup valueFresh
    exact ⟨extend_store_trans extension later,typed,functions⟩

theorem memoryWrite_as_payload (s : store) (f : frame) (position : Nat) (value : byte) :
    Segment.memoryWrite s f position value = memoryPayloadWrite s f position [value] := by
  simp only [Segment.memoryWrite,memoryPayloadWrite,Segment.splice_singleton_eq_set]

theorem memoryFill_preserves (s : store) (f : frame) (address destination value count : Nat)
    (object : meminst) (wf : wf_store s) (contents : StoreContentsTyped s)
    (mapped : f.MODULE.MEMS[0]? = some address) (found : s.MEMS[address]? = some object) :
    Extend_store s (Segment.memoryFill s f destination value count) ∧
      StoreContentsTyped (Segment.memoryFill s f destination value count) ∧
      (Segment.memoryFill s f destination value count).FUNCS = s.FUNCS := by
  induction count generalizing s object destination with
  | zero => exact ⟨extend_store_refl s wf,contents,rfl⟩
  | succ count ih =>
    have byteWf : Forall wf_byte [Segment.fillByte value] := by simpa [Forall] using Segment.fillByte_wf value
    have extension := memoryPayloadWrite_extends s f address destination object [Segment.fillByte value] wf contents mapped found byteWf
    have fresh := contents.memory_write wf f address destination object [Segment.fillByte value] mapped found byteWf
    rw [←memoryWrite_as_payload] at extension fresh
    have lookup : (Segment.memoryWrite s f destination (Segment.fillByte value)).MEMS[address]? =
        some {object with BYTES := object.BYTES.set destination (Segment.fillByte value)} := by
      rw [memoryWrite_as_payload,memoryPayloadWrite_as_set s f address destination object _ mapped found,Segment.splice_singleton_eq_set]
      simp only [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1]
    obtain ⟨later,typed,functions⟩ := ih (Segment.memoryWrite s f destination (Segment.fillByte value))
      (Segment.next32 destination) {object with BYTES := object.BYTES.set destination (Segment.fillByte value)}
      (extend_store_wf extension).2 fresh lookup
    exact ⟨extend_store_trans extension later,typed,functions⟩
end Itasca.Runtime.Abs.Stateful
