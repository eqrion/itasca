import Exec.Generated.Types
namespace Exec.Store
open Aeneas Aeneas.Std

/-- The only ordinary failure class available while allocating a certified
initializer or staging a store object. -/
def ResourceError : runtime.ExecError → Prop
  | .Exhausted _ => True
  | _ => False

def ErrorAllowed {α : Type} (allowed : runtime.ExecError → Prop) : core.result.Result α runtime.ExecError → Prop
  | .Ok _ => True
  | .Err error => allowed error

/-- A precommit trap is restricted to the Wasm1 segment-bound precheck. All
other precommit rejections are linking, foreign-store handles, or embedding-resource failures. -/
def PrecommitError (profile : Itasca.ValidationProfile) : runtime.ExecError → Prop
  | .Link _ => True
  | .WrongStore => True
  | .Exhausted _ => True
  | .Trap .MemoryOutOfBounds | .Trap .TableOutOfBounds => profile = .Wasm1
  | _ => False

theorem ResourceError.precommit {profile error} (resource : ResourceError error) : PrecommitError profile error := by
  cases error <;> simp_all [ResourceError, PrecommitError]

theorem PrecommitError.kind {profile error} (allowed : PrecommitError profile error) :
    error = .WrongStore ∨ (∃ link, error = .Link link) ∨ (∃ resource, error = .Exhausted resource) ∨
      (profile = .Wasm1 ∧ (error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds)) := by
  cases error <;> simp_all [PrecommitError]
  rename_i trap
  cases trap <;> simp_all [PrecommitError]
end Exec.Store
