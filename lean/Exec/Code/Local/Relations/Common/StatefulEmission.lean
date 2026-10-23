import Exec.Abs.Stateful.Signature
import Exec.Code.Local.Relations.Common.StatefulOpcode
import Exec.Code.Local.Relations.Common.ScalarEmission
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

end Exec.Code
