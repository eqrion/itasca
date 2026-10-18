module
public import Runtime.Types
public import Validator.Funs
@[expose] public section
open Aeneas Aeneas.Std
namespace Runtime.validator
def token_value := Validator.validator.token_value
def validate {V : Type} (v : Visitor V) :=
  Validator.validator.validate (Validator.validator.Visitor.mk v.visit)
end Runtime.validator
