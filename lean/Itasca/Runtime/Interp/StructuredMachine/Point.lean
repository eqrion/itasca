import Itasca.Runtime.Code.Local.Control.Table.StructuredCodeLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Abs.ModuleBindingsExtension
import Itasca.Runtime.Code.Body.Relations.Common.ExecutableEmission
namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std
abbrev ContextEmission := context → List valtype → instr → List Code.Bytecode → List valtype → Prop
end Itasca.Runtime.Interp.StructuredMachine

namespace Itasca.Runtime.Interp
/-- The emission relation of a compiled function: the complete compiler relation over the
function's retained indirect, SIMD, constant and jump-table metadata. -/
abbrev emission (compiled : runtime.bytecode.CompiledFunction) : StructuredMachine.ContextEmission :=
  Code.ExecutableEmission (Code.CompilerTables.ofFunction compiled)
end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.StructuredMachine
open Aeneas.Std

structure FramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : Abs.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Code.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Code.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val compiled.jump_tables.val targets (frame.vals.map Code.valueType) frame.code raw.pc.val next output

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem FramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : FramePoint before raw frame compiled C targets next output) :
    FramePoint after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

end Itasca.Runtime.Interp.StructuredMachine
