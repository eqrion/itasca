import Exec.Interp.Relations.Synthetic
import Exec.Interp.Relations.ScalarDispatch
namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Two little-endian slot words, including the interpreter's zero padding. -/
def vectorBits (words : List U64) (position : Nat) : BitVec 128 :=
  ((words[position]?).getD 0#u64).bv.setWidth 128 |||
    (((words[position+1]?).getD 0#u64).bv.setWidth 128 <<< 64)

@[step] theorem vector_effect (slots : Slice U64) (position : Usize)
    (space : position.val < Usize.max) :
    runtime.interp.vector slots position ⦃ value => value.bv = vectorBits slots.val position.val ⦄ := by
  unfold runtime.interp.vector
  step with get_effect as ⟨lo, hlo⟩
  simp only [lift, bind_ok]
  step as ⟨next, hnext⟩
  step with get_effect as ⟨hi, hhi⟩
  step as ⟨shifted, hshifted, shiftBits⟩
  simp only [UScalar.bv_or, UScalar.cast_bv_eq, shiftBits]
  simp only [vectorBits, hlo, hhi, hnext]
  rfl

end Itasca.Runtime.Interp
