import Exec.Store.Api.Define

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

@[simp] theorem vec_set_current {T : Type} (values : alloc.vec.Vec T) (index : Usize)
    (hindex : index.val < values.length) : values.set index values.val[index.val] = values := by
  apply alloc.vec.Vec.ext
  simp [alloc.vec.Vec.set_val_eq, List.set_getElem_self]

end Itasca.Runtime.Store
