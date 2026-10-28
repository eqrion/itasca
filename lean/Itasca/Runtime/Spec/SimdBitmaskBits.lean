import SpecExt.Builtins.Rotations
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

theorem integerBits_reverse (width : Nat) (bits : BitVec width) :
    integerBits width bits.reverse.toNat = (integerBits width bits.toNat).reverse := by
  apply List.ext_getElem
  · simp [integerBits_length]
  · intro i left right
    have valid : i < width := by simpa only [integerBits_length] using left
    rw [integerBits_getMsb _ _ _ valid,List.getElem_reverse]
    simp only [integerBits_length]
    rw [integerBits_getMsb _ _ _ (by omega)]
    simp [BitVec.getMsbD_reverse,BitVec.getLsbD_reverse,BitVec.getMsbD_eq_getLsbD,valid]

theorem irev_reverse (width : Nat) (bits : BitVec width) :
    irev_ width (.mk_uN bits.reverse.toNat) = .mk_uN bits.toNat := by
  unfold irev_ ibits_ inv_ibits_
  simp only [proj_uN_0,integerBits_reverse,List.reverse_reverse,integerBits_roundtrip bits.isLt]
end Itasca.Runtime.Spec.Simd
