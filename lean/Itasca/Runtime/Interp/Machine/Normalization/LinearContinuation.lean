import Itasca.Runtime.Interp.Machine.Point

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
