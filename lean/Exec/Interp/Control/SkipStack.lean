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

/-- An administrative forward skip preserves the whole stack and installs its
retained continuation without changing any represented values. -/
theorem FrameStackRel.skip {M : Type} {store : runtime.store.Store M}
    {exec : runtime.interp.Execution} {source : Abs.AFrame} {rest : List Abs.AFrame}
    (relation : FrameStackRel store exec (source :: rest))
    (raw : runtime.interp.Frame) (index : Usize) (target : U32)
    (last : index.val + 1 = exec.frames.length)
    (lookup : exec.frames.val[index.val]? = some raw)
    (binding : FrameBinding store exec raw source)
    (slots : FrameSlots exec raw source)
    {compiled functions targets next output}
    (program : FrameProgram store raw compiled (source.locals.map Code.valueType) source.resultTypes functions)
    (point : StructuredFramePoint { raw with pc := target } source compiled functions targets next output) :
    FrameStackRel store { exec with frames := exec.frames.set index { raw with pc := target } }
      (source :: rest) := by
  have top : exec.frames.val.getLast? = some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length - 1 = index.val := by change exec.frames.length - 1 = index.val; omega
    rw [position]
    exact lookup
  refine relation.step_active (after := { exec with frames := exec.frames.set index { raw with pc := target } }) raw { raw with pc := target } top
    (frames_set_last exec index _ last) rfl rfl rfl (Nat.le_refl _) ?_ ?_
  · intro position bits represented _
    exact represented
  · exact ⟨binding.advance index target lookup, slots, compiled, functions, targets, next, output,
      false, ⟨program.lookup, program.checked, program.fetchBound, program.localSlots, program.epilogue⟩,
      .ready point⟩

end Exec.Interp
