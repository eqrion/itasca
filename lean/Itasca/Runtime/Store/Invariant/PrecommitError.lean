import Itasca.Generated.Types
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The only ordinary failure class available while allocating a certified
initializer or staging a store object. -/
def ResourceError : runtime.ExecError → Prop
  | .Exhausted _ => True
  | _ => False

def ErrorAllowed {α : Type} (allowed : runtime.ExecError → Prop) : core.result.Result α runtime.ExecError → Prop
  | .Ok _ => True
  | .Err error => allowed error

/-- Precommit rejections are linking, foreign-store handles, or embedding-resource
failures. Segment traps arise only after publication. -/
def PrecommitError : runtime.ExecError → Prop
  | .Link _ => True
  | .WrongStore => True
  | .Exhausted _ => True
  | _ => False

theorem ResourceError.precommit {error} (resource : ResourceError error) : PrecommitError error := by
  cases error <;> simp_all [ResourceError, PrecommitError]

end Itasca.Runtime.Store
