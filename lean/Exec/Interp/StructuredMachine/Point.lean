import Exec.Code.Local.Control.Table.StructuredCodeWithTablesLabels
import Exec.Interp.Control.StructuredPoint
import Exec.Abs.ModuleBindingsExtension
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
abbrev ContextEmission := context → List valtype → instr → List Code.Bytecode → List valtype → Prop
/-- Each active function supplies its exact immutable compiler metadata. -/
abbrev FunctionEmission := runtime.bytecode.CompiledFunction → ContextEmission

variable {emission : FunctionEmission}
structure FramePoint (emission : FunctionEmission) (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : Abs.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Code.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val compiled.jump_tables.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem FramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : FramePoint emission before raw frame compiled C targets next output) :
    FramePoint emission after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

end Exec.Interp.StructuredMachine
