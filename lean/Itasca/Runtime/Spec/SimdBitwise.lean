import SpecExt.Builtins.BitwiseVector
import Itasca.Runtime.Spec.IntegerBits
namespace Itasca.Runtime.Spec.Simd
open SpecExt.Builtins

def binary (op : vvbinop) (a b : BitVec 128) : BitVec 128 :=
  match op with
  | .AND => a &&& b
  | .ANDNOT => a &&& ~~~b
  | .OR => a ||| b
  | .XOR => a ^^^ b

theorem not_value (a : BitVec 128) :
    vvunop_ .V128 .NOT (.mk_uN a.toNat) = .mk_uN (~~~a).toNat :=
  inot_bitvec a

theorem binary_value (op : vvbinop) (a b : BitVec 128) :
    vvbinop_ .V128 op (.mk_uN a.toNat) (.mk_uN b.toNat) =
      .mk_uN (binary op a b).toNat := by
  cases op
  · exact iand_bitvec a b
  · exact iandnot_bitvec a b
  · exact ior_bitvec a b
  · exact ixor_bitvec a b

theorem bitselect_value (a b c : BitVec 128) :
    vvternop_ .V128 .BITSELECT (.mk_uN a.toNat) (.mk_uN b.toNat) (.mk_uN c.toNat) =
      .mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat :=
  ibitselect_bitvec a b c

theorem const_wf (a : BitVec 128) :
    wf_admininstr (.VCONST .V128 (.mk_uN a.toNat)) := by
  apply wf_admininstr.admininstr_case_20 _ _ (by decide)
  exact unsigned_wf_of_lt 128 a.toNat (BitVec.toNat_lt_twoPow_of_le (by rfl))

theorem not_step (a : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VVUNOP .V128 .NOT]
      [.VCONST .V128 (.mk_uN (~~~a).toNat)] := by
  exact .vvunop _ _ _ (not_value a).symm (const_wf a)
    (.admininstr_case_21 ..) (const_wf _)

theorem binary_step (op : vvbinop) (a b : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VCONST .V128 (.mk_uN b.toNat),
      .VVBINOP .V128 op] [.VCONST .V128 (.mk_uN (binary op a b).toNat)] := by
  exact .vvbinop _ _ _ _ (binary_value op a b).symm (const_wf a) (const_wf b)
    (.admininstr_case_22 ..) (const_wf _)

theorem bitselect_step (a b c : BitVec 128) :
    Step_pure [.VCONST .V128 (.mk_uN a.toNat), .VCONST .V128 (.mk_uN b.toNat),
      .VCONST .V128 (.mk_uN c.toNat), .VVTERNOP .V128 .BITSELECT]
      [.VCONST .V128 (.mk_uN ((a &&& c) ||| (b &&& ~~~c)).toNat)] := by
  exact .vvternop _ _ _ _ _ (bitselect_value a b c).symm
    (const_wf a) (const_wf b) (const_wf c) (.admininstr_case_23 ..) (const_wf _)

end Itasca.Runtime.Spec.Simd
