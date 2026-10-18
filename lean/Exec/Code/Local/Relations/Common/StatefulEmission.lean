import Exec.Abs.Stateful.Signature
import Exec.Code.Local.Relations.Common.StatefulOpcode
import Exec.Code.Local.Lowering.Float.FloatCoreEmission
import Exec.Code.Local.Relations.Calls.IndirectCallEmissionTransport

namespace Exec.Code
open Aeneas.Std

/-- Reference and bulk instructions retain their exact function-local pair table.
This is syntactic compiler evidence, independent of execution correctness. -/
inductive StatefulEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | instruction (stack input output) (op : Abs.Stateful.Instruction)
      (signature : Abs.Stateful.Signature C op input output)
      (first second a b entry : U32)
      (firstSlot : first.val = slots C.LOCALS + slots stack)
      (secondSlot : op.arity ≥ 2 → second.val = first.val + 1)
      (arguments : StatefulArguments op a b)
      (pair : StatefulPair pairs op a b entry) :
      StatefulEmission pairs C (stack ++ input) op.source
        [statefulInstruction op first second a entry] (stack ++ output)

/-- Cumulative ordinary instructions; adding another family does not duplicate
structured control, saved-frame or execution-stack evidence. -/
inductive EmissionUnion
    (left right : context → List valtype → instr → List Bytecode → List valtype → Prop)
    (C : context) : List valtype → instr → List Bytecode → List valtype → Prop where
  | left {before instruction emitted after} (head : left C before instruction emitted after) :
      EmissionUnion left right C before instruction emitted after
  | right {before instruction emitted after} (head : right C before instruction emitted after) :
      EmissionUnion left right C before instruction emitted after

inductive CumulativeEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | left {before instruction emitted after} (head : FloatCoreEmission C before instruction emitted after) :
      CumulativeEmission pairs C before instruction emitted after
  | right {before instruction emitted after} (head : StatefulEmission pairs C before instruction emitted after) :
      CumulativeEmission pairs C before instruction emitted after
  | indirect {before instruction emitted after} (head : IndirectCallEmission pairs C before instruction emitted after) :
      CumulativeEmission pairs C before instruction emitted after

abbrev CumulativeCodeRel (pairs : List (U32 × U32)) (C : context) (returns : List valtype) :=
  StructuredCode (CumulativeEmission pairs C) C.TYPES C.FUNCS returns C.LOCALS

theorem StatefulEmission.length_one {pairs C before instruction emitted after}
    (emission : StatefulEmission pairs C before instruction emitted after) : emitted.length = 1 := by
  cases emission; rfl

theorem FloatCoreCodeRel.cumulative {pairs C returns code labels stack source pc next final}
    (relation : FloatCoreCodeRel C returns code labels stack source pc next final) :
    CumulativeCodeRel pairs C returns code labels stack source pc next final :=
  relation.map_emission (fun _ _ _ _ head => .left head)

end Exec.Code
