import Itasca.Runtime.Compiler.Local.Control.Table.StructuredCodeLabels
import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.SourceMachine.ModuleBindingsExtension
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission

/-!
Source contexts and code positions in a frame-point certificate.

Main declarations: `FramePoint` and `ContextEmission`. A direct consumer is `Interp.Machine.SuspendedPoint`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
abbrev ContextEmission := context → List valtype → instr → List Compiler.Bytecode → List valtype → Prop
end Itasca.Runtime.Interp.Machine

namespace Itasca.Runtime.Interp
/-- The emission relation of a compiled function: the complete compiler relation over the
function's retained indirect, SIMD, constant and jump-table metadata. -/
abbrev emission (compiled : runtime.bytecode.CompiledFunction) : Machine.ContextEmission :=
  Compiler.ExecutableEmission (Compiler.CompilerTables.ofFunction compiled)
end Itasca.Runtime.Interp

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

structure FramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (frame : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction)
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) : Prop where
  bindings : SourceMachine.ModuleBindings sourceStore frame.module C
  locals : C.LOCALS = frame.locals.map Compiler.valueType
  labels : LabelsMatch frame.vals frame.labels targets
  code : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS frame.resultTypes
    C.LOCALS compiled.code.val compiled.jump_tables.val targets (frame.vals.map Compiler.valueType) frame.code raw.pc.val next output

/-- Content mutations transport the same source/code position through the
specification's checked store extension; no code or frame state is changed. -/
theorem FramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw frame compiled C targets next output}
    (point : FramePoint before raw frame compiled C targets next output) :
    FramePoint after raw frame compiled C targets next output :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

end Itasca.Runtime.Interp.Machine
