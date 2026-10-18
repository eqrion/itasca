import Exec.Abs.Preservation
import Exec.Abs.Numeric.Unary

namespace Exec.Abs.Numeric
open SpecExt Exec.Spec

theorem unary_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty : Inn} {op : unop_Inn} {bits result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth ty)
    (h : FrameTyped s
      { f with code := .UNOP (numtype_Inn ty) (.mk_unop__0 ty op) :: code, vals := baseValues ++ [integerVal ty bits] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal ty result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      codeStack_after (value_types_concrete (baseValues ++ [integerVal ty bits])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using resultsTyped_take baseValues.length values
    have hresult := integer_val_typed hs ty result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal ty result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter

theorem conversion_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty target : Inn} {op : cvtop__} {bits result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth target)
    (h : FrameTyped s
      { f with code := .CVTOP (numtype_Inn target) (numtype_Inn ty) op :: code, vals := baseValues ++ [integerVal ty bits] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal target result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      codeStack_after (value_types_concrete (baseValues ++ [integerVal ty bits])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using resultsTyped_take baseValues.length values
    have hresult := integer_val_typed hs target result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal target result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter


end Exec.Abs.Numeric
