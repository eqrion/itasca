import Exec.Abs.Typing

namespace Exec.Abs.Simd
open SpecExt

/-- Principal stack signatures of pure SIMD source instructions. This relation
uses source constructors only and is independent of the byte decoder. -/
inductive PureSignature : instr → List valtype → valtype → Prop where
  | wholeUnary op : PureSignature (.VVUNOP .V128 op) [.V128] .V128
  | wholeBinary op : PureSignature (.VVBINOP .V128 op) [.V128,.V128] .V128
  | wholeTernary op : PureSignature (.VVTERNOP .V128 op) [.V128,.V128,.V128] .V128
  | wholeTest op : PureSignature (.VVTESTOP .V128 op) [.V128] .I32
  | unary sh op : PureSignature (.VUNOP sh op) [.V128] .V128
  | binary sh op : PureSignature (.VBINOP sh op) [.V128,.V128] .V128
  | test sh op : PureSignature (.VTESTOP sh op) [.V128] .I32
  | relation sh op : PureSignature (.VRELOP sh op) [.V128,.V128] .V128
  | shift sh op : PureSignature (.VSHIFTOP sh op) [.V128,.I32] .V128
  | bitmask sh : PureSignature (.VBITMASK sh) [.V128] .I32
  | swizzle sh : PureSignature (.VSWIZZLE sh) [.V128,.V128] .V128
  | shuffle sh lanes : PureSignature (.VSHUFFLE sh lanes) [.V128,.V128] .V128
  | splat sh : PureSignature (.VSPLAT sh) [valtype_numtype (shunpack sh)] .V128
  | extract sh sign lane : PureSignature (.VEXTRACT_LANE sh sign lane) [.V128] (valtype_numtype (shunpack sh))
  | replace sh lane : PureSignature (.VREPLACE_LANE sh lane) [.V128,valtype_numtype (shunpack sh)] .V128
  | extendUnary first second op : PureSignature (.VEXTUNOP first second op) [.V128] .V128
  | extendBinary first second op : PureSignature (.VEXTBINOP first second op) [.V128,.V128] .V128
  | narrow first second sign : PureSignature (.VNARROW first second sign) [.V128,.V128] .V128
  | convert first second op : PureSignature (.VCVTOP first second op) [.V128] .V128

theorem PureSignature.principal {source inputs output C signature}
    (shape : PureSignature source inputs output) (typed : Instr_ok C source signature) :
    signature = .mk_functype (.mk_list inputs) (.mk_list [output]) := by
  cases shape <;> cases typed <;> rfl

theorem PureSignature.arity {source inputs output} (shape : PureSignature source inputs output) :
    inputs.length ≤ 3 := by cases shape <;> simp

theorem PureSignature.output_numeric {source inputs output} (shape : PureSignature source inputs output) :
    output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty := by
  cases shape <;> first | exact Or.inl rfl | exact Or.inr ⟨.I32,rfl⟩ | exact Or.inr ⟨_,rfl⟩

theorem numeric_value_typed {s : store} {value : val} {output : valtype}
    (numeric : output = .V128 ∨ ∃ ty : numtype, output = valtype_numtype ty)
    (storeWf : wf_store s) (valid : wf_val value) (typeEq : valueType value = output) :
    Val_ok s value output := by
  rw [← typeEq]
  cases value with
  | CONST ty bits => exact .numtype s ty bits storeWf valid
  | VCONST ty bits => cases ty; exact .vectype s .V128 bits storeWf valid
  | REF_NULL ty =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · cases ty <;> simp_all [valueType,valtype_reftype]
    · cases ty <;> cases nt <;> simp_all [valueType,valtype_reftype,valtype_numtype]
  | REF_FUNC_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]
  | REF_HOST_ADDR address =>
    rcases numeric with numeric | ⟨nt,numeric⟩
    · simp_all [valueType]
    · cases nt <;> simp_all [valueType,valtype_numtype]

end Exec.Abs.Simd
