import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Equations
import Itasca.Support.TypeTranslation

/-!
Validator stack widths and their slot-count interpretation. Compiler layout and source-demand proofs use this bridge without importing body construction.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def compilerStackWidth : Itasca.code.StackType → Nat
  | .Val ty => width (Itasca.Translate.valueType ty)
  | .Bot => 1

def stackWords (values : List Itasca.code.StackType) : Nat :=
  (values.map compilerStackWidth).sum
end Itasca.Runtime.Compiler
