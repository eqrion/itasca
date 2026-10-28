import Exec.Code.Local.Relations.Common.SelectLowering
import Exec.Code.Local.Control.Common.Structured

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Explicit select emits the same width-specific instruction as implicit
select, while retaining its declared source result type. -/
inductive TypedSelectEmission (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | select (front : List valtype) (ty : valtype) (left right condition : U32)
      (leftPos : left.val = slots C.LOCALS + slots front)
      (rightPos : right.val = left.val + width ty)
      (conditionPos : condition.val = right.val + width ty) :
      TypedSelectEmission C (front ++ [ty,ty,.I32]) (.SELECT (some [ty]))
        [selectInstruction (decide (width ty = 2)) left right condition] (front ++ [ty])

end Itasca.Runtime.Code
