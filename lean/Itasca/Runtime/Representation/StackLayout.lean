import Itasca.Runtime.Representation.Layout
import Itasca.Runtime.Equations
import Itasca.Support.TypeTranslation

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

def compilerStackWidth : Itasca.code.StackType → Nat
  | .Val ty => width (Itasca.Translate.valueType ty)
  | .Bot => 1

def stackWords (values : List Itasca.code.StackType) : Nat :=
  (values.map compilerStackWidth).sum
end Itasca.Runtime.Code
