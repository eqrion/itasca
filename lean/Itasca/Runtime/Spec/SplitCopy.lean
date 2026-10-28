import Itasca.Runtime.Spec.SegmentCopySlice
namespace Itasca.Runtime.Spec.Segment

/-- A write in the left half of a split buffer reconstructs the corresponding
write in the original buffer. -/
theorem setSlice_split_left {T : Type} (before payload : List T) (split start : Nat)
    (splitBound : split ≤ before.length) (inside : start+payload.length ≤ split) :
    (before.take split).setSlice! start payload ++ before.drop split = before.setSlice! start payload := by
  have leftRoom : payload.length ≤ (before.take split).length-start := by simp only [List.length_take]; omega
  have wholeRoom : payload.length ≤ before.length-start := by omega
  simp only [List.setSlice!,Nat.min_eq_left leftRoom,Nat.min_eq_left wholeRoom,List.take_length]
  rw [List.take_take, Nat.min_eq_left (by omega : start ≤ split)]
  rw [List.drop_take]
  have combine := List.take_append_drop (split-(start+payload.length)) (before.drop (start+payload.length))
  rw [List.drop_drop] at combine
  have total : start+payload.length+(split-(start+payload.length))=split := by omega
  rw [total] at combine
  simpa only [List.append_assoc] using congrArg (fun rest => before.take start ++ payload ++ rest) combine

/-- A write starting at the right half reconstructs its original-buffer write. -/
theorem setSlice_split_right {T : Type} (before payload : List T) (split : Nat)
    (inside : split+payload.length ≤ before.length) :
    before.take split ++ (before.drop split).setSlice! 0 payload = before.setSlice! split payload := by
  have room : payload.length ≤ before.length-split := by omega
  simp [List.setSlice!,room,List.drop_drop,Nat.min_eq_left room,List.append_assoc]
end Itasca.Runtime.Spec.Segment
