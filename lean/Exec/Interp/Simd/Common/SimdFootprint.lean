import Exec.Interp.Simd.Common.SimdValueSlots
namespace Exec.Interp
open Aeneas Aeneas.Std

theorem simdResultSlots_length (words : List U64) (position : Nat) (width : U32) (value : U128) :
    (simdResultSlots words position width value).length = words.length := by
  unfold simdResultSlots
  split <;> split <;> simp only [List.length_set]

theorem WordsAt.simd_result_outside {words : List U64} {base : Nat} {bits : List Nat}
    (represented : WordsAt words base bits) (position : Nat) (width : U32) (value : U128)
    (above : base+bits.length ≤ position) :
    WordsAt (simdResultSlots words position width value) base bits := by
  unfold simdResultSlots
  split <;> split
  all_goals first
    | exact represented
    | exact represented.set_outside position _ (Or.inr above)
    | exact represented.set_outside (position+1) _ (Or.inr (by omega))
    | exact (represented.set_outside position _ (Or.inr above)).set_outside (position+1) _ (Or.inr (by omega))
end Exec.Interp
