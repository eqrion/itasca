import Exec.Store.Initialization.BulkTableLoop
import Exec.Spec.SegmentCopy

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

theorem copySegment_front (before source : List U64) (dst src count : Nat) :
    copySegment before source dst src (count+1) =
      copySegment (before.set dst source[src]!) source (dst+1) (src+1) count := by
  induction count with
  | zero => simp [copySegment]
  | succ count ih =>
    rw [copySegment,ih,copySegment]
    simp only [Nat.add_assoc, Nat.add_comm 1 count]

theorem copySegment_eq_copyInto (before source : List U64) (dst src count : Nat) :
    copySegment before source dst src count = Spec.Segment.copyInto before source dst src count := by
  induction count generalizing before dst src with
  | zero => rfl
  | succ count ih => rw [copySegment_front,Spec.Segment.copyInto,ih]

theorem copyInto_map {T U : Type} [Inhabited T] [Inhabited U] (decode : T → U)
    (before source : List T) (dst src count : Nat) (inside : src+count ≤ source.length) :
    (Spec.Segment.copyInto before source dst src count).map decode =
      Spec.Segment.copyInto (before.map decode) (source.map decode) dst src count := by
  induction count generalizing before dst src with
  | zero => rfl
  | succ count ih =>
    have bound : src < source.length := by omega
    rw [Spec.Segment.copyInto,Spec.Segment.copyInto,ih _ (dst+1) (src+1) (by omega)]
    congr 1
    simp [List.map_set,List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem bound]

end Itasca.Runtime.Store
