import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Equations.Interp

/-! Slot encoding and decoding for the extracted interpreter. -/

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact list update performed by the extracted slot writer. -/
def written (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) : List U64 :=
  if sourceType ty = .V128 then (words.set position lo).set (position + 1) hi
  else words.set position lo

@[step] theorem encode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (value : runtime.Value) (lo hi : U64)
    (he : runtime.value.encode value = .ok (lo, hi))
    (hb : position.val + Compiler.width (sourceType ty) ≤ slots.length) :
    runtime.interp.encode_slot slots position ty value ⦃ result =>
      result.val = written slots.val position.val ty lo hi ⦄ := by
  have hp : position.val < slots.length := by
    have := Compiler.width_positive (sourceType ty)
    omega
  unfold runtime.interp.encode_slot
  rw [he]
  step as ⟨old, back, hold, hback⟩
  subst back
  cases ty <;> simp only [Compiler.compiler_width_eq, Compiler.initializerWidth, sourceType, Compiler.width] at hb ⊢
  all_goals try simp [written, sourceType]
  step as ⟨next, hnext⟩
  step as ⟨after, hafter⟩
  subst after
  simp [hnext]

theorem index_eq (slots : Slice U64) (position : Usize) (word : U64)
    (hb : position.val < slots.length) (hv : slots.val[position.val]! = word) :
    Slice.index_usize slots position = .ok word := by
  obtain ⟨actual, hr, ha⟩ := WP.spec_imp_exists (Slice.index_usize_spec slots position hb)
  have he : actual = word := by simpa [ha, _root_.getElem!_pos slots.val position.val hb] using hv
  rw [he] at hr
  exact hr

/-- The extracted reader observes exactly the one or two words at its slot
boundary, then uses the extracted value decoder on those words. -/
@[step] theorem decode_slot_spec (slots : Slice U64) (position : Usize)
    (ty : Itasca.wasm_types.ValueType) (store : Usize) (lo hi : U64) (value : runtime.Value)
    (hb : position.val + Compiler.width (sourceType ty) ≤ slots.length)
    (hlo : slots.val[position.val]! = lo)
    (hhi : if sourceType ty = .V128 then slots.val[position.val + 1]! = hi else hi = 0#u64)
    (hd : runtime.value.decode ty lo hi store = .ok value) :
    runtime.interp.decode_slot slots position ty store ⦃ result => result = value ⦄ := by
  have hp : position.val < slots.length := by
    have := Compiler.width_positive (sourceType ty)
    omega
  have hread := index_eq slots position lo hp hlo
  cases ty <;> simp only [sourceType, reduceCtorEq, ↓reduceIte] at hhi
  all_goals first
    | solve | subst hi; simp [runtime.interp.decode_slot, Compiler.compiler_width_eq, Compiler.initializerWidth, hread, hd]
    | skip
  unfold runtime.interp.decode_slot
  simp [Compiler.compiler_width_eq, Compiler.initializerWidth]
  step as ⟨next, hnext⟩
  have hn : next.val < slots.length := by
    simp only [sourceType, Compiler.width] at hb
    omega
  have hnword : slots.val[next.val]! = hi := by simpa [hnext] using hhi
  have hreadHi := index_eq slots next hi hn hnword
  simp [hreadHi, hread, hd]

theorem written_length (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) : (written words position ty lo hi).length = words.length := by
  simp [written]; split <;> simp

theorem written_low (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) (hp : position < words.length) :
    (written words position ty lo hi)[position]! = lo := by
  unfold written
  split <;> simp [hp]

theorem written_high (words : List U64) (position : Nat) (ty : Itasca.wasm_types.ValueType)
    (lo hi : U64) (hv : sourceType ty = .V128) (hp : position + 1 < words.length) :
    (written words position ty lo hi)[position + 1]! = hi := by
  simp [written, hv, hp]

end Itasca.Runtime.Interp
