import Exec.Store.Invariant.InvalidWrite

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- A reference value whose private handle belongs to another store. Numeric
values and null references are never foreign. -/
def ForeignValue {M : Type} (s : runtime.store.Store M) : runtime.Value → Prop
  | .FuncRef (some a) => a.store ≠ s.id
  | .ExternRef (some a) => a.store ≠ s.id
  | _ => False

end Itasca.Runtime.Store
