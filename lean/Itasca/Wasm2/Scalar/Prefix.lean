import Itasca.Wasm2.Prefix
import Itasca.Wasm2.Scalar.Total

/-!
# Scalar typed prefixes

Re-proves the typed-prefix effect of the shared scalar handlers against the Wasm 2.0
`TypedPrefix` zipper. `TypedPrefix.nop`, `.unreachable` and the constant lemmas extend a prefix
by one instruction, `NumericEffect.wasm2_prefix`, `Popped.wasm2_prefix_drop` and
`SelectEffect.wasm2_prefix` do so for stack effects. `NumericReader` and
`StackReader` lift these facts to shared reader specifications.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

open Sequence

theorem TypedPrefix.nop {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.NOP]) poly vals := by
  apply h.append hC .NOP .instr_case_0
  intro ts ht
  refine ⟨ts, ht, ?_⟩
  simpa using Instrs_ok.frame C [.NOP] ts [] []
    (.instr C .NOP [] [] (.nop C hC .instr_case_0) hC .instr_case_0)
    hC (by simp [Forall]; exact .instr_case_0)

theorem TypedPrefix.unreachable {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals) (hC : wf_context C) :
    TypedPrefix C inputs (ops ++ [.UNREACHABLE]) true [] := by
  apply h.append hC .UNREACHABLE .instr_case_1
  intro ts _
  exact ⟨stackTypes vals, realizes_default poly vals,
    .instr C .UNREACHABLE (stackTypes vals) ts
      (.unreachable C _ ts hC .instr_case_1) hC .instr_case_1⟩

/-- Constants extend a prefix with arbitrary frame parameters. -/
theorem TypedPrefix.i32Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I32) :
    TypedPrefix C inputs (ops ++ [Spec.i32Const value]) poly (vals ++ [.Val .I32]) := by
  apply h.append hC _ (Spec.i32Const_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I32 hout
  exact ⟨before, hb, Spec.i32Const_framed C hC value before⟩

theorem TypedPrefix.i64Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : I64) :
    TypedPrefix C inputs (ops ++ [ScalarConst.i64 value]) poly (vals ++ [.Val .I64]) := by
  apply h.append hC _ (ScalarConst.i64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .I64 hout
  exact ⟨before, hb, ScalarConst.i64_framed C hC value before⟩

theorem TypedPrefix.f32Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U32) :
    TypedPrefix C inputs (ops ++ [ScalarConst.f32 value]) poly (vals ++ [.Val .F32]) := by
  apply h.append hC _ (ScalarConst.f32_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F32 hout
  exact ⟨before, hb, ScalarConst.f32_framed C hC value before⟩

theorem TypedPrefix.f64Const {C : context} {inputs : List valtype} {ops : List instr} {poly : Bool}
    {vals : List code.StackType} (h : TypedPrefix C inputs ops poly vals)
    (hC : wf_context C) (value : U64) :
    TypedPrefix C inputs (ops ++ [ScalarConst.f64 value]) poly (vals ++ [.Val .F64]) := by
  apply h.append hC _ (ScalarConst.f64_wf value)
  intro out hout
  obtain ⟨before, rfl, hb⟩ := Realizes.snoc_val .F64 hout
  exact ⟨before, hb, ScalarConst.f64_framed C hC value before⟩

/-- A typed prefix is a resume prefix with no saved arguments. -/
theorem ResumePrefix.of_prefix {C inputs ops poly vals}
    (h : TypedPrefix C inputs ops poly vals) : ResumePrefix C inputs ops poly vals [] :=
  ⟨h.wellFormed, fun ts ht => by simpa using h.typed ts ht⟩

end Itasca.Wasm2

namespace Itasca.StackSemantics

theorem NumericEffect.wasm2_prefix {initial : List valtype} {poly before inputs output after}
    (h : NumericEffect poly before inputs output after)
    (C : context) (hC : wf_context C) (ops : List instr) (op : instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) (hwf : wf_instr op)
    (hop : Instr_ok C op (.mk_functype (.mk_list (inputs.map Translate.valueType))
      (.mk_list [Translate.valueType output]))) :
    Wasm2.TypedPrefix C initial (ops ++ [op]) poly after := by
  obtain ⟨rest, rfl, htransfer⟩ := h
  apply htyped.append hC op hwf
  intro out hout
  obtain ⟨front, u, rfl, hfront, hu⟩ := hout.snoc_inv
  change u = Translate.valueType output at hu
  subst u
  refine ⟨front ++ inputs.map Translate.valueType, htransfer front hfront, ?_⟩
  exact .frame C [op] front _ _ (.instr C op _ _ hop hC hwf) hC (by simpa [Forall] using hwf)

theorem Popped.wasm2_prefix_drop {initial : List valtype} {poly before t after} (h : Popped poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) :
    Wasm2.TypedPrefix C initial (ops ++ [.DROP]) poly after := by
  apply htyped.append hC .DROP .instr_case_2
  intro out hout
  let u := match t with | .Val vt => Translate.valueType vt | .Bot => valtype.I32
  have haccept : Sequence.Accepts t u := by cases t <;> simp [Sequence.Accepts, u]
  refine ⟨out ++ [u], h.realizes out u haccept hout, ?_⟩
  simpa using Instrs_ok.frame C [.DROP] out [u] []
    (.instr C .DROP [u] [] (.drop C u hC .instr_case_2) hC .instr_case_2)
    hC (by simp [Forall]; exact .instr_case_2)

theorem SelectEffect.wasm2_prefix {initial : List valtype} {poly before t after} (h : SelectEffect poly before t after)
    (C : context) (hC : wf_context C) (ops : List instr)
    (htyped : Wasm2.TypedPrefix C initial ops poly before) :
    Wasm2.TypedPrefix C initial (ops ++ [.SELECT none]) poly after := by
  obtain ⟨hselect, rest, rfl, htransfer⟩ := h
  apply htyped.append hC (.SELECT none) (.instr_case_3 _)
  intro out hout
  obtain ⟨front, u, rfl, hf, hu⟩ := hout.snoc_inv
  refine ⟨front ++ [selectedType t, selectedType t, .I32], htransfer front hf, ?_⟩
  apply Instrs_ok.frame C [.SELECT none] front _ _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  apply Instrs_ok.sub C [.SELECT none] _ _ _ _
    (.instr C _ _ _ (selectedType_typed C hC t hselect) hC (.instr_case_3 _))
    _ _ hC (by simp [Forall]; exact .instr_case_3 _)
  · exact .mk_Resulttype_sub _ _ rfl (by simp [Forall₂, Valtype_sub.refl])
  · exact .mk_Resulttype_sub _ _ rfl (by simpa [Forall₂] using selectedType_sub hu)

end Itasca.StackSemantics
