import Itasca.Runtime.Abs.Numeric.Unary

namespace Itasca.Runtime.Abs.Numeric
open SpecExt Itasca.Runtime.Spec

theorem Conversion.source_wf (op : Conversion) : wf_instr op.source := by
  cases op
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_1 _ _ (by decide)) rfl rfl) (by decide)
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide)
  · exact .instr_case_18 _ _ _ (.cvtop___case_0 _ _ _ _ _ (.cvtop__Inn_1_Inn_2_case_0 _ _ _ (by decide)) rfl rfl) (by decide)

theorem Conversion.relation (op : Conversion) (bits : BitVec (sizenn (numtype_Inn op.input))) :
    fun_cvtop__ (numtype_Inn op.input) (numtype_Inn op.output) op.operator
      (.mk_num__0 op.input (.mk_uN bits.toNat))
      (some [.mk_num__0 op.output (.mk_uN (op.apply bits).toNat)]) := by
  cases op with
  | wrap => exact integer_wrap_relation bits
  | extendSigned => exact integer_extends_relation bits
  | extendUnsigned =>
    have bound : bits.toNat < 2^64 := by have := bits.isLt; change bits.toNat < 2^32 at this; omega
    change fun_cvtop__ .I32 .I64 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) _ (some [.mk_num__0 .I64 (.mk_uN (bits.setWidth 64).toNat)])
    rw [BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt bound]
    exact integer_extendu_relation bits

theorem Conversion.pure (op : Conversion) (bits : BitVec (sizenn (numtype_Inn op.input))) :
    Step_pure [admininstr_val (integerVal op.input bits.toNat), admininstr_instr op.source]
      [admininstr_val (integerVal op.output (op.apply bits).toNat)] := by
  apply Step_pure.cvtop_val (numtype_Inn op.input) (.mk_num__0 op.input (.mk_uN bits.toNat))
    (numtype_Inn op.output) op.operator (.mk_num__0 op.output (.mk_uN (op.apply bits).toNat))
    (some [.mk_num__0 op.output (.mk_uN (op.apply bits).toNat)])
  · exact op.relation bits
  · simp
  · simp
  · simp
  · exact wf_admininstr_val (integer_val_wf op.input _ (word_bound op.input bits))
  · exact wf_admininstr_instr op.source_wf
  · exact wf_admininstr_val (integer_val_wf op.output _ (word_bound op.output (op.apply bits)))

end Itasca.Runtime.Abs.Numeric
