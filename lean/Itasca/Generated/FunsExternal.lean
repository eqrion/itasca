-- Handwritten models for the operations requested by Aeneas.
-- Unlike Types.lean and Funs.lean, this file is not generated.
module
public import Aeneas
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

namespace Itasca.Primitive
/-- Count the set bits in the low `width` bits of a natural number. -/
def countBits : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value => value % 2 + countBits width (value / 2)

/-- Count the zero low bits, returning `width` for an all-zero word. -/
def trailingZeros : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value => if value % 2 = 0 then 1 + trailingZeros width (value / 2) else 0

theorem countBits_le (width value : Nat) : countBits width value ≤ width := by
  induction width generalizing value with
  | zero => simp [countBits]
  | succ width ih =>
    simp only [countBits]
    have := ih (value / 2)
    have := Nat.mod_lt value (by decide : 0 < 2)
    omega

theorem trailingZeros_le (width value : Nat) : trailingZeros width value ≤ width := by
  induction width generalizing value with
  | zero => simp [trailingZeros]
  | succ width ih =>
    simp only [trailingZeros]
    split
    · have := ih (value / 2); omega
    · omega
end Itasca.Primitive

@[rust_fun "core::num::{u32}::count_ones"]
def core.num.U32.count_ones (x : U32) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Itasca.Primitive.countBits 32 x.val)⟩
@[rust_fun "core::num::{u64}::count_ones"]
def core.num.U64.count_ones (x : U64) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Itasca.Primitive.countBits 64 x.val)⟩
@[rust_fun "core::num::{u32}::trailing_zeros"]
def core.num.U32.trailing_zeros (x : U32) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Itasca.Primitive.trailingZeros 32 x.val)⟩
@[rust_fun "core::num::{u64}::trailing_zeros"]
def core.num.U64.trailing_zeros (x : U64) : Result U32 :=
  .ok ⟨BitVec.ofNat 32 (Itasca.Primitive.trailingZeros 64 x.val)⟩

example : core.num.U64.count_ones 18446744073709551615#u64 = .ok 64#u32 := by rfl
example : core.num.U32.trailing_zeros 0#u32 = .ok 32#u32 := by rfl
example : core.num.U64.trailing_zeros 9223372036854775808#u64 = .ok 63#u32 := by rfl
