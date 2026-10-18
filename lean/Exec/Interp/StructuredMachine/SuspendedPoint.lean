import Exec.Interp.StructuredMachine.Point
import Exec.Interp.Relations.SuspendedPoint
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
variable {emission : FunctionEmission}

/-- A mutable caller retains its module context and its typed continuation
while its child's results have not yet been written into the operand area. -/
structure SuspendedFramePoint (emission : FunctionEmission) (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output waiting : List valtype) : Prop where
  bindings : Abs.ModuleBindings sourceStore source.module C
  locals : C.LOCALS = source.locals.map Code.valueType
  labels : LabelsMatch source.vals source.labels targets
  code : Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
    compiled.code.val compiled.jump_tables.val targets (source.vals.map Code.valueType ++ waiting) source.code raw.pc.val next output

theorem SuspendedFramePoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint emission before raw source compiled C targets next output waiting) :
    SuspendedFramePoint emission after raw source compiled C targets next output waiting :=
  ⟨point.bindings.extend extension,point.locals,point.labels,point.code⟩

theorem SuspendedFramePoint.resume {sourceStore raw source compiled C targets next output waiting}
    (point : SuspendedFramePoint emission sourceStore raw source compiled C targets next output waiting)
    (results : List val) (types : results.map Code.valueType = waiting) (heights : Abs.FrameHeights source) :
    FramePoint emission sourceStore raw {source with vals := source.vals ++ results} compiled C targets next output := by
  refine ⟨point.bindings,point.locals,point.labels.append results heights,?_⟩
  simpa only [List.map_append,types] using point.code

theorem FramePoint.suspend {sourceStore raw source compiled C targets next output}
    (point : FramePoint emission sourceStore raw source compiled C targets next output)
    (front args : List val) (after : List instr) (pc : U32) (returns : List valtype)
    (split : source.vals = front ++ args)
    (heights : ∀ label ∈ source.labels, label.height ≤ front.length)
    (continuation : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS source.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets (front.map Code.valueType ++ returns) after pc.val next output) :
    SuspendedFramePoint emission sourceStore {raw with pc := pc} {source with vals := front,code := after}
      compiled C targets next output returns := by
  refine ⟨point.bindings,point.locals,?_,⟨continuation,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩⟩
  apply point.labels.reprefix
  intro label member
  rw [split,List.take_append_of_le_length (heights label member)]

/-- The second dispatch of a compiled branch is represented explicitly; its
operand transfer has already occurred in the abstract machine. -/
inductive ControlPoint (emission : FunctionEmission) (sourceStore : _root_.store) (raw : runtime.interp.Frame)
    (source : Abs.AFrame) (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype) : Bool → Prop where
  | ready (point : FramePoint emission sourceStore raw source compiled C targets next output) :
      ControlPoint emission sourceStore raw source compiled C targets next output false
  | jump (target : U32) (fetched : compiled.code.val[raw.pc.val]? = some (.Jump target))
      (continuation : FramePoint emission sourceStore {raw with pc := target} source compiled C targets next output) :
      ControlPoint emission sourceStore raw source compiled C targets next output true

theorem ControlPoint.extend {before after : _root_.store} (extension : Extend_store before after)
    {raw source compiled C targets next output pending}
    (point : ControlPoint emission before raw source compiled C targets next output pending) :
    ControlPoint emission after raw source compiled C targets next output pending := by
  cases point with
  | ready h => exact .ready (h.extend extension)
  | jump target fetched h => exact .jump target fetched (h.extend extension)
end Exec.Interp.StructuredMachine
