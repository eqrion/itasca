import Exec.Interp.Simd.Common.SimdSlots
namespace Exec.Interp
open Aeneas Aeneas.Std

def simdInput (words : List U64) (position : Nat) (width : U32) : U128 :=
  if width = 2#u32 then ⟨vectorBits words position⟩
  else UScalar.cast .U128 ((words[position]?).getD 0#u64)

@[step] theorem simd_input_effect (slots : Slice U64) (position : Usize) (width : U32)
    (space : position.val < Usize.max) :
    (if width = 2#u32 then runtime.interp.vector slots position
      else do let word ← runtime.interp.get slots position
              pure (UScalar.cast .U128 word))
      ⦃ value => value = simdInput slots.val position.val width ⦄ := by
  split
  · rename_i two
    step with vector_effect as ⟨value,bits⟩
    simp only [simdInput,if_pos two]
    exact (UScalar.eq_equiv_bv_eq _ _).mpr bits
  · rename_i other
    step with get_effect as ⟨value,word⟩
    simp [simdInput,other,word]

end Exec.Interp
