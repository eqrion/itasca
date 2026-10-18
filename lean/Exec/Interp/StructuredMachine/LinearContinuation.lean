import Exec.Interp.StructuredMachine.Point
namespace Exec.Interp.StructuredMachine
open Aeneas.Std
variable {emission : FunctionEmission}
theorem linear_continuation {sourceStore raw f compiled C targets next output}
    (point : FramePoint emission sourceStore raw f compiled C targets next output)
    (pc : U32) (locals values : List val) (source : List instr) (middle : List valtype)
    (rest : Code.StructuredCodeWithTables (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets middle source pc.val next output)
    (localTypes : locals.map Code.valueType = f.locals.map Code.valueType)
    (valueTypes : values.map Code.valueType = middle) (labels : LabelsMatch values f.labels targets) :
    FramePoint emission sourceStore {raw with pc := pc} {f with locals := locals,vals := values,code := source}
      compiled C targets next output := by
  refine ⟨point.bindings,point.locals.trans localTypes.symm,labels,?_⟩
  simpa only [valueTypes] using
    (show Code.StructuredCodeWithTables.Point (emission compiled C) C.TYPES C.FUNCS f.resultTypes C.LOCALS
      compiled.code.val compiled.jump_tables.val targets middle source pc.val next output from
      ⟨rest,point.code.targets,point.code.normal,point.code.exit,point.code.root⟩)

end Exec.Interp.StructuredMachine
