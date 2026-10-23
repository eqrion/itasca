import Exec.Interp.Calls.CallStack
import Exec.Interp.Relations.StackPreservation

namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Updating the fetched last frame preserves the exact concrete stack prefix. -/
theorem frames_set_last (exec : runtime.interp.Execution) (index : Usize)
    (updated : runtime.interp.Frame) (last : index.val + 1 = exec.frames.length) :
    (exec.frames.set index updated).val = exec.frames.val.dropLast ++ [updated] := by
  simp only [alloc.vec.Vec.set_val_eq, List.dropLast_eq_take]
  have within : index.val < exec.frames.val.length := by change index.val < exec.frames.length; omega
  have position : index.val = exec.frames.val.length - 1 := by change index.val = exec.frames.length - 1; omega
  rw [List.set_eq_take_append_cons_drop, if_pos within, position]
  simp only [show exec.frames.val.length - 1 + 1 = exec.frames.val.length by omega,
    List.drop_length]

end Exec.Interp
