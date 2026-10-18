import Exec.Interp.Core.Point
import Exec.Interp.Control.StructuredLinear
import Exec.Interp.Numeric.Integer.NumericCodePoint
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem structuredCode_linear_inv {emit types functions returns locals code labels stack pc next output op after}
    (linear : linearSource op = true)
    (relation : Code.StructuredCode emit types functions returns locals code labels stack (op :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Code.StructuredCode emit types functions returns locals code labels stack (op :: after) target.val next output) ∨
    (∃ middle emitted tail, emit stack op emitted middle ∧ Code.Segment code pc emitted tail ∧
      Code.StructuredCode emit types functions returns locals code labels middle after tail next output) := by
  cases relation with
  | linear head fragment rest => exact Or.inr ⟨_,_,_,head,fragment,rest⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
  | _ => simp_all [linearSource]

theorem core_structured_linear_continuation {sourceStore raw f compiled C targets next output}
    (point : CoreFramePoint sourceStore raw f compiled C targets next output)
    (pc : U32) (locals values : List val) (source : List instr) (middle : List valtype)
    (rest : Code.StructuredCode (Code.CoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets middle source pc.val next output)
    (localTypes : locals.map Code.valueType = f.locals.map Code.valueType)
    (valueTypes : values.map Code.valueType = middle) (labels : LabelsMatch values f.labels targets) :
    CoreFramePoint sourceStore {raw with pc := pc} {f with locals := locals,vals := values,code := source}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals.trans localTypes.symm,labels,?_⟩
  simpa only [valueTypes] using
    (show Code.StructuredCode.Point (Code.CoreEmission C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val targets middle source pc.val next output from
      ⟨rest,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩)

theorem coreEmission_numeric_pure {C before after emitted} (op : Abs.Numeric.Instruction)
    (emission : Code.CoreEmission C before op.source emitted after) :
    Code.LinearEmission C.LOCALS before op.source emitted after := by
  generalize equality : op.source = instruction at emission
  cases emission with
  | pure head => simpa only [equality] using head
  | _ =>
    have decoded := congrArg Abs.Numeric.decodeInstruction equality
    rw [Abs.Numeric.decodeInstruction_source] at decoded
    simp [Abs.Numeric.decodeInstruction,Abs.Memory.Load.source,Abs.Memory.Store.source] at decoded
end Exec.Interp
