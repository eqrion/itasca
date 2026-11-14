import Itasca.Runtime.Compiler.Local.Control.Table.StructuredFunction
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.Compiler.Body.Relations.Executable.RecordingEmission
import Itasca.Runtime.Interp.Relations.SuspendedPoint

/-!
Sections, each formerly its own module: Point, SuspendedPoint.
-/

/-! ## Point -/

section

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

end

/-! ## SuspendedPoint -/

section

/-!
A mutable caller retains its module context and its typed continuation while its child's results have not yet been written into the operand area.

Main declarations: `SuspendedFramePoint` and `ControlPoint`. A direct consumer is `Interp.Machine.Calls.CallPoint`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

/-- A mutable caller retains its module context and its typed continuation
while its child's results have not yet been written into the operand area. -/
structure SuspendedFramePoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output waiting : List valtype) : Prop where
  bindings : SourceMachine.ModuleBindings sourceStore source.module C
  locals : C.LOCALS = source.locals.map Compiler.valueType
  labels : LabelsMatch source.vals source.labels targets
  code : Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
    compiled.code.val compiled.jump_tables.val targets (source.vals.map Compiler.valueType ++ waiting) source.code raw.pc.val next output

theorem SuspendedFramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint before raw source compiled C targets next output waiting) :
    SuspendedFramePoint after raw source compiled C targets next output waiting :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

theorem SuspendedFramePoint.resume {sourceStore raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint sourceStore raw source compiled C targets next output waiting)
    (results : List val) (types : results.map Compiler.valueType = waiting) (heights : SourceMachine.FrameHeights source) :
    FramePoint sourceStore raw {source with vals := source.vals ++ results} compiled C targets next output := by
  refine ⟨point.bindings,point.locals,point.labels.append results heights,?_⟩
  simpa only [List.map_append,types] using point.code

theorem FramePoint.suspend {sourceStore raw source compiled C targets next output}
    (point : FramePoint sourceStore raw source compiled C targets next output)
    (front args : List val) (after : List instr) (pc : U32) (returns : List valtype)
    (split : source.vals = front ++ args)
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Compiler.valueType ++ returns) after pc.val next output) :
    SuspendedFramePoint sourceStore {raw with pc := pc} {source with vals := front,code := after}
      compiled C targets next output returns := by
  refine ⟨point.bindings,point.locals,?_,⟨continuation,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩⟩
  apply point.labels.reprefix
  intro label member
  rw [split,List.take_append_of_le_length (heights label member)]

/-- The second dispatch of a compiled branch is represented explicitly; its
operand transfer has already occurred in the abstract machine. -/
inductive ControlPoint (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : SourceMachine.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype) : Bool → Prop where
  | ready (point : FramePoint sourceStore raw source compiled C targets next output) :
      ControlPoint sourceStore raw source compiled C targets next output false
  | jump (target : U32) (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
      (continuation : FramePoint sourceStore {raw with pc := target} source compiled C targets next output) :
      ControlPoint sourceStore raw source compiled C targets next output true

theorem ControlPoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output pending}
    (point : ControlPoint before raw source compiled C targets next output pending) :
    ControlPoint after raw source compiled C targets next output pending := by
  cases point with
  | ready h => exact .ready (h.extend extension)
  | jump target fetched h => exact .jump target fetched (h.extend extension)
end Itasca.Runtime.Interp.Machine

end
