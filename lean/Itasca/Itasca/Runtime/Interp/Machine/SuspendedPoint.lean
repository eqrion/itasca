import Itasca.Runtime.Interp.Recording
import Itasca.Runtime.Compiler.Local.Control.Structured.NestedScopes
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.StructureAndTyping
import Itasca.Runtime.Compiler.Body.Relations.ExecutableEmission
import Itasca.Runtime.Interp.Relations.ReadbackAndBindings

/-! ## Point -/

section

/-!
Source contexts and code positions in a frame-point certificate.

Main declarations: `FramePoint` and `ContextEmission`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem FramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : FramePoint before raw frame compiled C targets next output) :
    FramePoint after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

end Itasca.Interp.Machine

end

/-! ## SuspendedPoint -/

section

/-!
A mutable caller retains its module context and its typed continuation while its child's results have not yet been written into the operand area.

Main declarations: `SuspendedFramePoint` and `ControlPoint`.
-/

namespace Itasca.Interp.Machine
open Aeneas.Std

theorem SuspendedFramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint before raw source compiled C targets next output waiting) :
    SuspendedFramePoint after raw source compiled C targets next output waiting :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

theorem SuspendedFramePoint.resume {sourceStore raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint sourceStore raw source compiled C targets next output waiting)
    (results : List val) (types : results.map Representation.valueType = waiting) (heights : SourceMachine.FrameHeights source) :
    FramePoint sourceStore raw {source with vals := source.vals ++ results} compiled C targets next output := by
  refine ⟨point.bindings,point.locals,point.labels.append results heights,?_⟩
  simpa only [List.map_append,types] using point.code

theorem FramePoint.suspend {sourceStore raw source compiled C targets next output}
    (point : FramePoint sourceStore raw source compiled C targets next output)
    (front args : List val) (after : List instr) (pc : U32) (returns : List valtype)
    (split : source.vals = front ++ args)
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Representation.valueType ++ returns) after pc.val next output) :
    SuspendedFramePoint sourceStore {raw with pc := pc} {source with vals := front,code := after}
      compiled C targets next output returns := by
  refine ⟨point.bindings,point.locals,?_,⟨continuation,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩⟩
  apply point.labels.reprefix
  intro label member
  rw [split,List.take_append_of_le_length (heights label member)]

theorem ControlPoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output pending}
    (point : ControlPoint before raw source compiled C targets next output pending) :
    ControlPoint after raw source compiled C targets next output pending := by
  cases point with
  | ready h => exact .ready (h.extend extension)
  | jump target fetched h => exact .jump target fetched (h.extend extension)
end Itasca.Interp.Machine

end
