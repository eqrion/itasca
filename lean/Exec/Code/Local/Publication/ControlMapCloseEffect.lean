import Exec.Code.Local.Publication.ControlMapPublicationClose

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Exact scope-close effects establish the invariant for the remaining
owners, using only reader progress and the independently bounded body extent. -/
theorem ControlMapPublication.close_effect {A : Type}
    {before after : runtime.compiler.FunctionCompiler A}
    (held : ControlMapPublication before) (stable : CompilerStable before after)
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (frames : before.frames.val = rest.val ++ [frame]) (remaining : after.frames = rest)
    (entry closed : runtime.compiler.ControlMap)
    (found : before.function.controls.val[frame.map.val]? = some entry)
    (controls : after.function.controls.val = before.function.controls.val.set frame.map.val closed)
    (startPc : closed.start_pc = entry.start_pc) (startSource : closed.source_start = entry.source_start)
    (position : closed.end_pc.val = before.function.code.length)
    (endSource : closed.source_end.val = before.function.body_start.val+positionSource)
    (progress : before.next_source.val < positionSource)
    (endBound : before.function.body_start.val+positionSource ≤ before.function.body_end.val)
    (code : before.function.code.length ≤ after.function.code.length)
    (cursor : before.next_source.val ≤ after.next_source.val) : ControlMapPublication after := by
  have bounded := (held.entries frame.map.val entry found).close_fields startPc startSource
    position endSource progress endBound
  apply held.close stable frame.map.val entry closed (rest.val.map (fun frame => frame.map.val))
    found controls _ _ startSource bounded code cursor
  · simp [activeControlMaps,frames]
  · simp [activeControlMaps,remaining]

end Exec.Code
