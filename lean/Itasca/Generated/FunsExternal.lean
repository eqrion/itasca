-- Handwritten models for the two operations requested by Aeneas.
-- Unlike Types.lean and Funs.lean, this file is not generated.
module
public import Aeneas
@[expose] public section

namespace Aeneas.Std.alloc.vec

-- Allocation capacity and allocator identity are absent from Aeneas's Vec
-- model. Both operations preserve that model's bound on the list length.
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::pop"]
def Vec.pop {T : Type} (_allocator : Type) (v : Vec T) :
    Result (Option T × Vec T) :=
  .ok (v.val.getLast?, Vec.from v.val.dropLast (by
    have h := v.property
    simp only [List.length_dropLast]
    omega))

@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::is_empty"]
def Vec.is_empty {T : Type} (_allocator : Type) (v : Vec T) : Result Bool :=
  .ok v.val.isEmpty

end Aeneas.Std.alloc.vec
