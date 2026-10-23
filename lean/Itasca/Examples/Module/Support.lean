import Itasca.Main

/-!
# Shared helpers for module examples

Helpers for writing whole-module byte fixtures: `bytes` builds a slice literal, and `leb`, `one`,
`padded` and `omitted` build the `ModuleBinary` encoding derivations for one-byte LEB128 values,
one-element vectors, present sections and omitted sections.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleSupport

open ModuleBinary

/-- A bounded slice literal. Fixtures are checked by the kernel, with no external evaluator. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- A byte below 128 is its own one-byte unsigned LEB128 encoding. -/
theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

/-- A one-element vector is the count byte 1 followed by its element. -/
theorem one {α : Type} {R : α → List U8 → Prop} {x bs}
    (h : R x bs) : VecEncoding R [x] (1#u8 :: bs) :=
  ⟨[1#u8], bs, leb 1#u8, by simpa using Rep.cons h Rep.nil, rfl⟩

/-- A present section with a one-byte size and no leading custom sections. -/
theorem padded {α : Type} {R : α → List U8 → Prop} (id size : U8)
    (absent : α) {x bs} (h : R x bs) (hlen : bs.length = size.val)
    (hsize : size.val < 128 := by decide) :
    PaddedEncoding id R absent x (id :: size :: bs) :=
  ⟨[], _, .nil, .present ⟨[size], bs, hlen ▸ leb size hsize, h, rfl⟩, rfl⟩

/-- An omitted section with no surrounding custom sections. -/
theorem omitted {α : Type} (id : U8) (R : α → List U8 → Prop) (absent : α) :
    PaddedEncoding id R absent absent [] := ⟨[], [], .nil, .absent, rfl⟩

end Itasca.Examples.ModuleSupport
