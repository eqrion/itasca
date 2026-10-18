import Exec.Code.Local.Relations.Common.CoreEmission
import Exec.Code.Local.Control.Common.StructuredCodeLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension

namespace Exec.Interp
open Aeneas.Std

/-- Mutable instruction code points retain the complete source module context.
In particular global indices are tied to their actual declared types. -/
structure CoreFramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : Abs.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Code.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem CoreFramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : CoreFramePoint before raw frame compiled C targets next output) :
    CoreFramePoint after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

/-- Every already-certified pure slice point embeds without changing its code
or continuation proof, once its source module context is supplied. -/
theorem CoreFramePoint.of_slice {sourceStore raw frame compiled functions targets next output}
    (point : StructuredFramePoint raw frame compiled functions targets next output)
    (C : context) (bindings : Abs.ModuleBindings sourceStore frame.module C)
    (locals : C.LOCALS = frame.locals.map Code.valueType) (functionTypes : C.FUNCS = functions) :
    CoreFramePoint sourceStore raw frame compiled C targets next output := by
  refine ⟨bindings,locals,point.labels,?_⟩
  have original : Code.StructuredPoint C.TYPES C.FUNCS frame.resultTypes C.LOCALS
      compiled.code.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output := by
    simpa only [bindings.types,locals,functionTypes] using point.code
  exact (Code.StructuredCode.Point.of_legacy original).map_emission (fun _ _ _ _ h => .pure h)

end Exec.Interp
