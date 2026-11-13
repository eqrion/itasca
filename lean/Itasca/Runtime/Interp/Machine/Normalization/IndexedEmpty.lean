import Itasca.Runtime.Interp.Machine.SuspendedPoint
import Itasca.Runtime.Interp.Machine.Emission.Local

/-!
Sections, each formerly its own module: IndexedLinear, LinearContinuation, IndexedEmpty.
-/

/-! ## IndexedLinear -/

section

/-!
Inversion of a linear indexed structured-code relation.

Main declarations: `structured_code_linear_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std

theorem structured_code_linear_inv {emit types functions returns locals code jumpTables labels stack pc next output op after}
    (linear : linearSource op = true)
    (relation : Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack (op :: after) target.val next output) ∨
    (∃ middle emitted tail, emit stack op emitted middle ∧ Compiler.Segment code pc emitted tail ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels middle after tail next output) := by
  cases relation with
  | linear head ordinary fragment rest => exact Or.inr ⟨_,_,_,head,fragment,rest⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
  | _ => simp_all [linearSource]
end Itasca.Runtime.Interp.Machine

end

/-! ## LinearContinuation -/

section

/-!
The source continuation after a linear instruction sequence.

Main declarations: `linear_continuation`. A direct consumer is `Interp.Machine.Numeric`.
-/

namespace Itasca.Runtime.Interp.Machine
open Aeneas.Std
theorem linear_continuation {sourceStore raw f compiled C targets next output}
    (point : FramePoint sourceStore raw f compiled C targets next output)
    (pc : U32) (locals values : List val) (source : List instr) (middle : List valtype)
    (rest : Compiler.StructuredCode (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets middle source pc.val next output)
    (localTypes : locals.map Compiler.valueType = f.locals.map Compiler.valueType)
    (valueTypes : values.map Compiler.valueType = middle) (labels : LabelsMatch values f.labels targets) :
    FramePoint sourceStore {raw with pc := pc} {f with locals := locals,vals := values,code := source}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals.trans localTypes.symm,labels,?_⟩
  simpa only [valueTypes] using
    (show Compiler.StructuredCode.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets middle source pc.val next output from
      ⟨rest,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩)

end Itasca.Runtime.Interp.Machine

end

/-! ## IndexedEmpty -/

section

/-!
Inversion of an empty indexed structured-code relation.

Main declarations: `structured_code_empty_inv`. A direct consumer is `Interp.Machine.Normalization`.
-/

namespace Itasca.Runtime.Interp.Machine

theorem structured_code_empty_inv {emit types functions returns locals code jumpTables labels stack pc next output}
    (relation : Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack [] pc next output) :
    (∃ target, pc < target.val ∧ code[pc]? = some (.Jump target) ∧
      Compiler.StructuredCode emit types functions returns locals code jumpTables labels stack [] target.val next output) ∨
    (pc = next ∧ stack = output ∧ Compiler.NormalLive labels) := by
  cases relation with
  | nil _ _ _ _ live => exact Or.inr ⟨rfl,rfl,live⟩
  | skip forward instruction rest => exact Or.inl ⟨_,forward,instruction,rest⟩
end Itasca.Runtime.Interp.Machine

end
