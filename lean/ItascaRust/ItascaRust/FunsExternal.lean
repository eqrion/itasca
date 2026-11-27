-- Handwritten models for the operations requested by Aeneas.
-- Unlike Types.lean and Funs.lean, this file is not generated.
module
public import Aeneas
public import ItascaRust.Types
@[expose] public section
open Aeneas Aeneas.Std

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

namespace Aeneas.Std.alloc.sync.Arc

@[rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::new"]
def new {T : Type} (value : T) : Result (alloc.sync.Arc T) := .ok value

@[rust_fun "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def Insts.CoreOpsDerefDeref.deref {T : Type} (_allocator : Type)
    (shared : alloc.sync.Arc T) : Result T := .ok shared

end Aeneas.Std.alloc.sync.Arc

/-- The Rust body is a single strong-reference clone. Its payload is immutable. -/
def Itasca.stream.share_code (shared : alloc.sync.Arc Itasca.metadata.CodeMetadata) :
    Result (alloc.sync.Arc Itasca.metadata.CodeMetadata) := .ok shared
