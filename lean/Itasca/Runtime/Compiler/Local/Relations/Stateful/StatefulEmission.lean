import Itasca.Runtime.SourceMachine.Stateful.Signature
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulOpcode
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallEmissionTransport

/-!
Reference and bulk instructions retain their exact function-local pair table. This is syntactic compiler evidence, independent of execution correctness.

Main declarations: `StatefulEmission`. A direct consumer is `Compiler.Local.Relations.Calls.IndirectCallExclusions`.
-/

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
