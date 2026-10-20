import Exec.Code.Local.Publication.ControlMapPublicationEnter

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Exact frame and map appends from the enter callbacks establish ownership
and the new map's bounds from its emitted position and source origin. -/
theorem ControlMapPublication.enter_effect {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (frame : runtime.compiler.Frame) (entry : runtime.compiler.ControlMap)
    (frames : after.frames.val = before.frames.val ++ [frame])
    (owner : frame.map.val = before.function.controls.length)
    (controls : after.function.controls.val = before.function.controls.val ++ [entry])
    (position : entry.start_pc.val ≤ after.function.code.length)
    (origin : entry.source_start.val = before.function.body_start.val+before.next_source.val)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  have active : activeControlMaps after = activeControlMaps before ++ [before.function.controls.length] := by
    simp [activeControlMaps,frames,owner]
  apply held.push stable entry controls active code cursor
  obtain ⟨_,_,_,_,_,_,_,start,_,_⟩ := stable.fields
  unfold OpenControlMapBounds
  rw [origin,start]
  exact ⟨position,by omega,by omega⟩

end Exec.Code
