import Exec.Representation.Layout
import Exec.Generated.Funs
import Itasca.Support.TypeTranslation

namespace Exec.Code
open Aeneas Aeneas.Std

def compilerStackWidth : Itasca.code.StackType → Nat
  | .Val ty => width (Itasca.Translate.valueType ty)
  | .Bot => 1

def stackWords (values : List Itasca.code.StackType) : Nat :=
  (values.map compilerStackWidth).sum
end Exec.Code
