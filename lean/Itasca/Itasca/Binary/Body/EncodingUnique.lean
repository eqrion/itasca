import Itasca.Binary.Body.Encoding
import Itasca.Binary.ModuleUnique
import Itasca.Binary.Scalar.MemoryMeaning

/-!
# Uniqueness of Wasm 2.0 instruction decoding

Prefix uniqueness of the Wasm 2.0 immediates (`Immediate.prefix_unique`), including reference,
bulk memory and block type immediates, and of tokens (`token_prefix_unique`). It gives `At.unique`
for one token, `Consumed.unique` for a token sequence and `BodyEncoding.unique` for a complete
body, as in `Binary/Body.Scalar/EncodingUnique` and `Binary/Body.Scalar/EncodingUnique`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Body

open Binary

/-- Reference instruction immediates are prefix-unique. -/
theorem ReferencesBinary.Immediate.prefix_unique (opcode : U8) :
    PrefixUnique (ReferencesBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy eq
  exact PrefixUnique.of_source (f := id) (WebAssembly.Binary.ReferencesBinary.Immediate.prefix_unique (sourceByte opcode))
    Function.injective_id (Binary.Source.referenceImmediate hx) (Binary.Source.referenceImmediate hy) eq

/-- Bulk instruction immediates are prefix-unique. -/
theorem BulkBinary.Immediate.prefix_unique (opcode : U32) :
    PrefixUnique (BulkBinary.Immediate opcode) := by
  intro x y a b rest tail hx hy eq
  exact PrefixUnique.of_source (f := id) (WebAssembly.Binary.BulkBinary.Immediate.prefix_unique opcode.val)
    Function.injective_id (Binary.Source.bulkImmediate hx) (Binary.Source.bulkImmediate hy) eq

end Itasca.Body

open Aeneas Aeneas.Std

namespace Itasca.Body

open Binary

theorem BlockEncoding.prefix_unique : PrefixUnique BlockEncoding :=
  PrefixUnique.of_source WebAssembly.Binary.BlockEncoding.prefix_unique Source.blockTypeInjective

theorem Immediate.prefix_unique (opcode : U8) : PrefixUnique (Immediate opcode) := by
  intro x y a b rest tail hx hy eq
  exact PrefixUnique.of_source (WebAssembly.Binary.Immediate.prefix_unique (sourceByte opcode))
    Source.tokenInjective (Source.tokenImmediate hx) (Source.tokenImmediate hy) eq

theorem token_prefix_unique : PrefixUnique TokenEncoding := by
  intro x y a b rest tail hx hy eq
  exact PrefixUnique.of_source WebAssembly.Binary.token_prefix_unique Source.tokenInjective
    (Source.tokenEncoding hx) (Source.tokenEncoding hy) eq

/-- A byte string is the encoding of at most one token sequence. -/
theorem tokens_unique : Itasca.Binary.Unique (Itasca.Binary.Rep TokenEncoding) :=
  token_prefix_unique.rep_unique (by rintro _ _ ⟨op, immediate, rfl, _⟩; simp)

/-- The token read at a cursor and its end cursor are determined by `data` and `start`. -/
theorem At.unique {data start t u next last}
    (ht : At data start t next) (hu : At data start u last) : t = u ∧ next = last := by
  obtain ⟨bs, ht, hb⟩ := ht
  obtain ⟨cs, hu, hc⟩ := hu
  obtain ⟨rfl, rfl, _⟩ := token_prefix_unique ht hu (hb.suffix.symm.trans hc.suffix)
  exact ⟨rfl, UScalar.eq_of_val_eq (hb.length.trans hc.length.symm)⟩

/-- A consumed span that ends where it starts has no tokens. -/
theorem Consumed.nil_of_equal_cursor {data start tokens next}
    (h : Consumed data start tokens next) (hp : start = next) : tokens = [] := by
  cases h with
  | nil => rfl
  | snoc hs ht => have := hs.span; have := ht.span; subst next; omega

/-- Two consumed spans over the same interval have the same tokens. -/
theorem Consumed.unique {data start xs ys next}
    (hx : Consumed data start xs next) (hy : Consumed data start ys next) : xs = ys := by
  induction xs generalizing start ys with
  | nil =>
    have hn := hx.empty_eq rfl
    exact (hy.nil_of_equal_cursor hn.symm).symm
  | cons x xs ih =>
    obtain ⟨p, hp, hxs⟩ := Consumed.cons_iff.mp hx
    cases ys with
    | nil =>
      have hn := hy.empty_eq rfl
      have := hp.span
      have := hxs.span
      subst next
      omega
    | cons y ys =>
      obtain ⟨q, hq, hys⟩ := Consumed.cons_iff.mp hy
      obtain ⟨rfl, rfl⟩ := hp.unique hq
      rw [ih hxs hys]

/-- A complete body encoding determines one instruction tree, regardless of typing. -/
theorem BodyEncoding.unique {data xs ys}
    (hx : BodyEncoding data xs) (hy : BodyEncoding data ys) : xs = ys := by
  obtain ⟨xt, xp, hx, hxp, hxs⟩ := hx
  obtain ⟨yt, yp, hy, hyp, hys⟩ := hy
  have hp : xp = yp := UScalar.eq_of_val_eq (hxp.trans hyp.symm)
  subst yp
  have ht := hx.unique hy
  subst yt
  exact hxs.unique hys

end Itasca.Body
