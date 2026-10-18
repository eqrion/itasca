import Exec.Interp.Core.Point
import Exec.Code.Local.Lowering.Float.FloatCoreEmission
import Exec.Code.Local.Control.Common.StructuredCodeLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension

namespace Exec.Interp
open Aeneas.Std

/-- Float instruction code points retain the complete module context and structured continuation. -/
structure FloatFramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : Abs.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Code.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem FloatFramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : FloatFramePoint before raw frame compiled C targets next output) :
    FloatFramePoint after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

/-- Every already-certified pure slice point embeds without changing its code
or continuation proof, once its source module context is supplied. -/
theorem FloatFramePoint.of_slice {sourceStore raw frame compiled functions targets next output}
    (point : StructuredFramePoint raw frame compiled functions targets next output)
    (C : context) (bindings : Abs.ModuleBindings sourceStore frame.module C)
    (locals : C.LOCALS = frame.locals.map Code.valueType) (functionTypes : C.FUNCS = functions) :
    FloatFramePoint sourceStore raw frame compiled C targets next output := by
  refine ⟨bindings,locals,point.labels,?_⟩
  have original : Code.StructuredPoint C.TYPES C.FUNCS frame.resultTypes C.LOCALS
      compiled.code.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output := by
    simpa only [bindings.types,locals,functionTypes] using point.code
  exact (Code.StructuredCode.Point.of_legacy original).map_emission (fun _ _ _ _ h => .core (.pure h))

end Exec.Interp

namespace Exec.Interp
open Aeneas.Std

theorem FloatFramePoint.of_core {sourceStore raw frame compiled C targets next output}
    (point : CoreFramePoint sourceStore raw frame compiled C targets next output) :
    FloatFramePoint sourceStore raw frame compiled C targets next output :=
  ⟨point.bindings, point.locals, point.labels, point.code.map_emission (fun _ _ _ _ h => .core h)⟩

theorem float_structured_linear_continuation {sourceStore raw f compiled C targets next output}
    (point : FloatFramePoint sourceStore raw f compiled C targets next output)
    (pc : U32) (locals values : List val) (source : List instr) (middle : List valtype)
    (rest : Code.StructuredCode (Code.FloatCoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets middle source pc.val next output)
    (localTypes : locals.map Code.valueType = f.locals.map Code.valueType)
    (valueTypes : values.map Code.valueType = middle) (labels : LabelsMatch values f.labels targets) :
    FloatFramePoint sourceStore {raw with pc := pc} {f with locals := locals,vals := values,code := source}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals.trans localTypes.symm,labels,?_⟩
  simpa only [valueTypes] using
    (show Code.StructuredCode.Point (Code.FloatCoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets middle source pc.val next output from
      ⟨rest,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩)
end Exec.Interp
