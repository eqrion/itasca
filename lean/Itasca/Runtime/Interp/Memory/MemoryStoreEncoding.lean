import Itasca.Runtime.Interp.Memory.MemoryEncoding
import Itasca.Runtime.Spec.SegmentCopySlice

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

def scalarStorePayload (value : U64) (width : Nat) : List U8 :=
  (List.range width).map (scalarStoreByte value)

private theorem scalarStorePayload_at (value : U64) (width index : Nat) (inside : index < width) :
    (scalarStorePayload value width)[index]! = scalarStoreByte value index := by
  simp [scalarStorePayload,List.getElem!_eq_getElem?_getD,inside]

theorem scalarStoreBytes_copyInto (bytes : List U8) (start : Nat) (value : U64) (width index count : Nat)
    (inside : index + count ≤ width) :
    scalarStoreBytes bytes start value index count =
      Spec.Segment.copyInto bytes (scalarStorePayload value width) (start+index) index count := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih =>
    simp only [scalarStoreBytes,Spec.Segment.copyInto]
    rw [scalarStorePayload_at value width index (by omega)]
    simpa only [Nat.add_assoc] using ih (bytes.set (start+index) (scalarStoreByte value index)) (index+1) (by omega)

theorem scalarStoreBytes_setSlice (bytes : List U8) (start : Nat) (value : U64) (width : Nat)
    (inside : start + width ≤ bytes.length) :
    scalarStoreBytes bytes start value 0 width = bytes.setSlice! start (scalarStorePayload value width) := by
  rw [scalarStoreBytes_copyInto bytes start value width 0 width (by omega)]
  simp only [Nat.add_zero]
  rw [Spec.Segment.copyInto_eq_setSlice _ _ _ _ _ (by simp [scalarStorePayload]) inside]
  simp only [List.slice_zero_j, Nat.zero_add]
  rw [List.take_of_length_le (by simp [scalarStorePayload])]

private theorem integerBytes_at (count value index : Nat) (inside : index < count) :
    (SpecExt.Builtins.integerBytes count value)[index]? = some (.mk_byte ((value / 256^index) % 256)) := by
  induction index generalizing count value with
  | zero => cases count <;> simp_all [SpecExt.Builtins.integerBytes]
  | succ index ih =>
    cases count with
    | zero => omega
    | succ count =>
      simpa only [SpecExt.Builtins.integerBytes,List.getElem?_cons_succ,Nat.pow_succ,
        Nat.div_div_eq_div_mul,Nat.mul_comm] using ih count (value/256) (by omega)

theorem scalarStorePayload_source (value : U64) (width : Nat) :
    Store.decodeBytes (scalarStorePayload value width) = SpecExt.Builtins.integerBytes width value.val := by
  apply List.ext_getElem?
  intro index
  by_cases inside : index < width
  · rw [integerBytes_at width value.val index inside]
    simp only [Store.decodeBytes,scalarStorePayload,List.getElem?_map]
    simp only [List.getElem?_range inside,Option.map_some]
    congr 2
    change (value.val >>> (index*8)) % 256 = (value.val / 256^index) % 256
    rw [Nat.shiftRight_eq_div_pow]
    congr 2
    rw [Nat.mul_comm, Nat.pow_mul]
  · have outside : width ≤ index := by omega
    rw [List.getElem?_eq_none (by simpa [Store.decodeBytes,scalarStorePayload] using outside),
      List.getElem?_eq_none (by simpa only [SpecExt.Builtins.integerBytes_length] using outside)]

theorem scalarStoreBytes_source (bytes : List U8) (start : Nat) (value : U64) (width : Nat)
    (inside : start+width ≤ bytes.length) :
    Store.decodeBytes (scalarStoreBytes bytes start value 0 width) =
      (Store.decodeBytes bytes).setSlice! start (SpecExt.Builtins.integerBytes width value.val) := by
  rw [scalarStoreBytes_setSlice bytes start value width inside]
  unfold Store.decodeBytes
  rw [List.map_setSlice!]
  rw [show (scalarStorePayload value width).map (fun b => byte.mk_byte b.val) =
    SpecExt.Builtins.integerBytes width value.val from scalarStorePayload_source value width]
end Itasca.Runtime.Interp
