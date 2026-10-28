import Exec.Abs.Typing

namespace Itasca.Runtime.Abs
open SpecExt
open Itasca.DeclarativeComplete

/-- Removing nop preserves the generated source typing judgment, including
arbitrary framing and bottom subtyping in the original derivation. -/
theorem nop_typing_tail {C : context} {before after : List valtype} {code : List instr}
    (h : Instrs_ok C (.NOP :: code) ⟨.mk_list before, .mk_list after⟩) :
    Instrs_ok C code ⟨.mk_list before, .mk_list after⟩ := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  cases hop
  simpa using narrow_input hrest hin

theorem nop_code_preservation {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack (.NOP :: code) results) :
    CodeStackTyped C labels stack code results := by
  cases h with
  | outer hc => exact .outer (nop_typing_tail hc)
  | label height nesting hc cont rest => exact .label height nesting (nop_typing_tail hc) cont rest

theorem nop_frame_preservation {s : store} {f : AFrame} {incoming : List valtype}
    {code : List instr} (h : FrameTyped s { f with code := .NOP :: code } incoming) :
    FrameTyped s { f with code := code } incoming := by
  cases h with
  | mk C bindings localTypes locals values returns codeTyped hw =>
    exact .mk C bindings localTypes locals values returns (nop_code_preservation codeTyped) hw

/-- The nop case of abstract-machine preservation is proved from source typing. -/
theorem nop_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (results : List val)
    (h : ATyped ⟨s, ambient, { f with code := .NOP :: code } :: rest, results⟩) :
    ATyped ⟨s, ambient, { f with code := code } :: rest, results⟩ := by
  obtain ⟨hs, functions, ha, frames, values, active, heights⟩ := h
  cases frames with
  | cons hf hr =>
    exact ⟨hs, functions, ha, .cons (nop_frame_preservation hf) hr, values, (fun _ => active (by simp)),
      replace_frame_heights heights (frameTyped_heights (nop_frame_preservation hf))⟩

@[simp] theorem pop_append (values : List val) (value : val) :
    pop (values ++ [value]) = some (values, value) := by
  simp [pop]

theorem const_typing_tail {C : context} {before after : List valtype} {code : List instr}
    {ty : numtype} {value : num_}
    (h : Instrs_ok C (.CONST ty value :: code) ⟨.mk_list before, .mk_list after⟩) :
    Instrs_ok C code ⟨.mk_list (before ++ [valtype_numtype ty]), .mk_list after⟩ := by
  obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal h
  cases hop
  apply narrow_input hrest
  simpa using result_sub_append hin (result_sub_refl [valtype_numtype ty])

theorem const_code_preservation {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr} {ty : numtype} {value : num_}
    (h : CodeStackTyped C labels stack (.CONST ty value :: code) results) :
    CodeStackTyped C labels (stack ++ [valtype_numtype ty]) code results := by
  cases h with
  | outer hc => exact .outer (const_typing_tail hc)
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    simpa only [List.append_assoc] using
      (CodeStackTyped.label height nesting (const_typing_tail hc) cont rest)

theorem codeStack_wf {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results) : Forall wf_instr code := by
  cases h with
  | outer hc => exact (wellFormed hc).2
  | label _ _ hc _ _ => exact (wellFormed hc).2

theorem const_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {ty : numtype} {value : num_} (hs : wf_store s)
    (h : FrameTyped s { f with code := .CONST ty value :: code } []) :
    FrameTyped s { f with code := code, vals := f.vals ++ [.CONST ty value] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns codeTyped hw =>
    have hconst := codeStack_wf codeTyped (.CONST ty value) (by simp)
    cases hconst with
    | instr_case_13 _ _ hnum =>
      have hval : Val_ok s (.CONST ty value) (valtype_numtype ty) :=
        .numtype _ _ _ hs (.val_case_0 _ _ hnum)
      apply FrameTyped.mk (f := { f with code := code, vals := f.vals ++ [.CONST ty value] })
        (incoming := []) C bindings localTypes locals ?_ returns ?_ hw
      · simpa [List.map_append, valueType, ResultsTyped] using
          (List.rel_append values (List.Forall₂.cons hval List.Forall₂.nil))
      · simpa [List.map_append, valueType, ResultsTyped] using const_code_preservation codeTyped

theorem const_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : numtype) (value : num_)
    (results : List val)
    (h : ATyped ⟨s, ambient, { f with code := .CONST ty value :: code } :: rest, results⟩) :
    ATyped ⟨s, ambient,
      { f with code := code, vals := f.vals ++ [.CONST ty value] } :: rest, results⟩ := by
  obtain ⟨hs, functions, ha, frames, values, active, heights⟩ := h
  cases frames with
  | cons hf hr =>
    exact ⟨hs, functions, ha, .cons (const_frame_preservation hs hf) hr,
      values, (fun _ => active (by simp)),
      replace_frame_heights heights (frameTyped_heights (const_frame_preservation hs hf))⟩

theorem codeStack_head {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin⟩
  | @label label labels saved operands _ _ _ _ hc _ _ =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    exact ⟨saved ++ front, ins, outs, hop, by simp only [heq, List.append_assoc]⟩

theorem resultsTyped_split {s : store} {before after : List valtype} {values : List val}
    (h : ResultsTyped s (before ++ after) values) :
    ∃ first last, values = first ++ last ∧
      ResultsTyped s before first ∧ ResultsTyped s after last := by
  induction before generalizing values with
  | nil => exact ⟨[], values, rfl, .nil, h⟩
  | cons ty before ih =>
    cases h with
    | cons hv hs =>
      obtain ⟨first, last, rfl, hf, hl⟩ := ih hs
      exact ⟨_ :: first, last, rfl, .cons hv hf, hl⟩

/-- Inverting source typing yields actual operands of the instruction's declared
input types, with no bottom values or stack-polymorphic witness assumptions. -/
theorem frame_typed_operands {s : store} {f : AFrame} {op : instr} {code : List instr}
    (h : FrameTyped s { f with code := op :: code } []) :
    ∃ C first operands ins outs,
      ModuleBindings s f.module C ∧ C.LOCALS = f.locals.map valueType ∧
      Instr_ok (labelContext C f.labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      f.vals = first ++ operands ∧ ResultsTyped s ins operands := by
  cases h with
  | mk C bindings locals hlocals values returns hc hw =>
    have concrete : Forall (fun ty => ty ≠ valtype.BOT) (f.vals.map valueType) := by
      intro ty hty
      obtain ⟨value, _, rfl⟩ := List.mem_map.mp hty
      exact valueType_ne_bot value
    have hc' : CodeStackTyped C f.labels (f.vals.map valueType) (op :: code) f.resultTypes := by
      simpa only [List.append_nil] using hc
    obtain ⟨front, ins, outs, hop, heq⟩ := codeStack_head concrete hc'
    have values' : ResultsTyped s (front ++ ins) f.vals := by rw [← heq]; exact values
    obtain ⟨first, operands, hsplit, _, hoperands⟩ := resultsTyped_split values'
    exact ⟨C, first, operands, ins, outs, bindings, locals, hop, hsplit, hoperands⟩

/-- Every saved label lies below the primitive instruction's operands. This
strengthens stack inversion with the absolute heights needed by branches. -/
theorem codeStack_head_bounds {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ (∀ label ∈ labels, label.height ≤ front.length) := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, by simp⟩
  | @label label labels saved operands _ _ height nesting hc _ _ =>
    obtain ⟨front, ins, outs, hop, hin, _⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    refine ⟨saved ++ front, ins, outs, hop, by simp only [heq, List.append_assoc], ?_⟩
    intro target ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp only [List.length_append, height]; omega
    · have hh := nesting target ht
      simp only [List.length_append, height]; omega

/-- Normalizing the first generated typing rule also retains the typed
continuation after replacing its operand suffix by the declared outputs. -/
theorem codeStack_after {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ CodeStackTyped C labels (front ++ outs) code results := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, .outer hrest⟩
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    exact ⟨saved ++ front, ins, outs, hop,
      by simp only [heq, List.append_assoc],
      by simpa only [List.append_assoc] using CodeStackTyped.label height nesting hrest cont rest⟩

theorem resultsTyped_take {s : store} {values : List val} (n : Nat)
    (h : ResultsTyped s (values.map valueType) values) :
    ResultsTyped s ((values.take n).map valueType) (values.take n) := by
  simpa only [ResultsTyped, List.map_take] using List.forall₂_take n h

theorem codeStack_after_bounds {C : context} {labels : List Label}
    {stack results : List valtype} {op : instr} {code : List instr}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack (op :: code) results) :
    ∃ front ins outs,
      Instr_ok (labelContext C labels) op ⟨.mk_list ins, .mk_list outs⟩ ∧
      stack = front ++ ins ∧ CodeStackTyped C labels (front ++ outs) code results ∧
      (∀ label ∈ labels, label.height ≤ front.length) := by
  cases h with
  | outer hc =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    exact ⟨front, ins, outs, hop, concrete_result_sub_eq concrete hin, .outer hrest, by simp⟩
  | @label label labels saved operands _ _ height nesting hc cont rest =>
    obtain ⟨front, ins, outs, hop, hin, hrest⟩ := head_normal hc
    have cop : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right _ hty)
    have heq := concrete_result_sub_eq cop hin
    refine ⟨saved ++ front, ins, outs, hop,
      by simp only [heq, List.append_assoc],
      by simpa only [List.append_assoc] using CodeStackTyped.label height nesting hrest cont rest, ?_⟩
    intro target ht
    rcases List.mem_cons.mp ht with rfl | ht
    · simp only [List.length_append, height]; omega
    · have hh := nesting target ht
      simp only [List.length_append, height]; omega

end Itasca.Runtime.Abs
