import Itasca.Runtime.SourceMachine.Progress

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

/-- Dropping an actual top value preserves the generated continuation type. -/
theorem drop_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {value : val}
    (h : FrameTyped s { f with code := .DROP :: code, vals := baseValues ++ [value] } []) :
    FrameTyped s { f with code := code, vals := baseValues } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [value])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_right_eq] at hstack
    have hlen : (baseValues.map valueType).length = front.length := by
      have hh := congrArg List.length hstack
      simpa using hh
    have hbase : baseValues.map valueType = front := (List.append_inj hstack hlen).1
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues }) C
      bindings localTypes locals hvalues returns ?_ hw
    simpa only [List.append_nil, hbase] using hafter

/-- Reading a local appends a value of exactly the type required by local.get. -/
theorem local_get_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {index : Nat} (h : FrameTyped s { f with code := .LOCAL_GET (.mk_uN index) :: code } []) :
    FrameTyped s { f with code := code, vals := f.vals ++ [f.locals[index]!] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete f.vals) hc
    cases hop with
    | local_get _ _ ty hi ht _ _ =>
      have hi' : index < f.locals.length := by simpa [labelContext, proj_uN_0, localTypes] using hi
      have hit : index < C.LOCALS.length := by simpa [labelContext, proj_uN_0] using hi
      have hv : Val_ok s f.locals[index]! ty := by
        have hh := locals.get hi' hit
        simp only [labelContext, proj_uN_0, getElem!_pos C.LOCALS index hit] at ht
        simpa only [List.get_eq_getElem, getElem!_pos f.locals index hi', ht] using hh
      have hty := value_type_of_typed hv
      apply FrameTyped.mk (f := { f with code := code, vals := f.vals ++ [f.locals[index]!] }) C
        bindings localTypes locals ?_ returns ?_ hw
      · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, hty] using
          List.rel_append values (List.Forall₂.cons hv List.Forall₂.nil)
      · simp only [List.append_nil] at hstack
        simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil, hstack, hty] using hafter

/-- Every bounded integer arithmetic result has the type expected by the
continuation, independently of which arithmetic equation produced its bits. -/
theorem integer_binop_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty : Inn} {op : binop_Inn} {a b result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth ty)
    (h : FrameTyped s
      { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty op) :: code, vals := baseValues ++ [integerVal ty a, integerVal ty b] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal ty result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [integerVal ty a, integerVal ty b])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    have hresult := integer_val_typed hs ty result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal ty result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType] using
        List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, hstack] using hafter

theorem integer_testop_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty : Inn} {op : testop_Inn} {bits result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth .I32)
    (h : FrameTyped s
      { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty op) :: code, vals := baseValues ++ [integerVal ty bits] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal .I32 result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [integerVal ty bits])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    have hresult := integer_val_typed hs .I32 result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal .I32 result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter

theorem integer_relop_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {ty : Inn} {op : relop_Inn} {a b result : Nat}
    (hs : wf_store s) (hr : result < 2 ^ integerWidth .I32)
    (h : FrameTyped s
      { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: code, vals := baseValues ++ [integerVal ty a, integerVal ty b] } []) :
    FrameTyped s { f with code := code, vals := baseValues ++ [integerVal .I32 result] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [integerVal ty a, integerVal ty b])) hc
    cases hop
    simp only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
      List.append_cancel_right_eq] at hstack
    have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
      simpa using results_typed_take baseValues.length values
    have hresult := integer_val_typed hs .I32 result hr
    apply FrameTyped.mk (f := { f with code := code, vals := baseValues ++ [integerVal .I32 result] }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
        numtype_Inn, valtype_numtype] using List.rel_append hvalues (List.Forall₂.cons hresult List.Forall₂.nil)
    · simpa only [List.map_append, List.map_cons, List.map_nil, List.append_nil,
        integerVal, valueType, numtype_Inn, valtype_numtype, hstack] using hafter

/-- Updating one local preserves the entire pointwise value typing relation. -/
theorem results_typed_set {s : store} {types : List valtype} {values : List val}
    (h : ResultsTyped s types values) (index : Nat) (hi : index < types.length)
    (value : val) (hv : Val_ok s value types[index]) :
    ResultsTyped s types (values.set index value) := by
  induction h generalizing index with
  | nil => simp at hi
  | @cons old ty values types hold htail ih =>
    cases index with
    | zero => exact .cons hv htail
    | succ index =>
      exact .cons hold (ih index (by simpa using hi) hv)

/-- Writing a local of its existing type preserves its declared type vector
and the frame's syntactic well-formedness. -/
theorem local_write_invariants {s : store} {f : AFrame} {C : context}
    {index : Nat} {value : val}
    (types : C.LOCALS = f.locals.map valueType)
    (locals : ResultsTyped s C.LOCALS f.locals)
    (hi : index < C.LOCALS.length) (hv : Val_ok s value C.LOCALS[index])
    (hw : wf_frame f.toFrame) :
    C.LOCALS = (f.locals.set index value).map valueType ∧
      ResultsTyped s C.LOCALS (f.locals.set index value) ∧
      wf_frame ({ f with locals := f.locals.set index value }).toFrame := by
  have hlocals := results_typed_set locals index hi value hv
  have htypes := results_type_of_typed hlocals
  refine ⟨htypes.symm, hlocals, ?_⟩
  cases hw with
  | frame_case_ _ _ _ hm =>
    exact .frame_case_ _ _ (results_typed_wf hlocals) hm

theorem results_typed_self_mem {s : store} {values : List val}
    (h : ResultsTyped s (values.map valueType) values) {value : val}
    (hm : value ∈ values) : Val_ok s value (valueType value) := by
  induction values with
  | nil => simp at hm
  | cons first values ih =>
    cases h with
    | cons hfirst htail =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hfirst
      · exact ih htail hm

theorem local_set_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {value : val} {index : Nat}
    (h : FrameTyped s { f with code := .LOCAL_SET (.mk_uN index) :: code, vals := baseValues ++ [value] } []) :
    FrameTyped s { f with code := code, locals := f.locals.set index value, vals := baseValues } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [value])) hc
    cases hop with
    | local_set _ _ ty hi ht _ _ =>
      have hit : index < C.LOCALS.length := by simpa [labelContext, proj_uN_0] using hi
      simp only [labelContext, proj_uN_0, getElem!_pos C.LOCALS index hit] at ht
      simp only [List.map_append, List.map_cons, List.map_nil] at hstack
      have hlen : (baseValues.map valueType).length = front.length := by
        have hh := congrArg List.length hstack; simpa using hh
      obtain ⟨hbase, hvalue⟩ := List.append_inj hstack hlen
      simp only [List.cons.injEq, and_true] at hvalue
      have hv : Val_ok s value C.LOCALS[index] := by
        rw [ht, ← hvalue]
        exact results_typed_self_mem values (by simp)
      obtain ⟨types', locals', hw'⟩ := local_write_invariants localTypes locals hit hv hw
      have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
        simpa using results_typed_take baseValues.length values
      apply FrameTyped.mk (f := { f with code := code, locals := f.locals.set index value, vals := baseValues }) C
        bindings types' locals' hvalues returns ?_ hw'
      simpa only [List.append_nil, hbase] using hafter

theorem local_tee_frame_preservation {s : store} {f : AFrame} {code : List instr}
    {baseValues : List val} {value : val} {index : Nat}
    (h : FrameTyped s { f with code := .LOCAL_TEE (.mk_uN index) :: code, vals := baseValues ++ [value] } []) :
    FrameTyped s { f with code := code, locals := f.locals.set index value, vals := baseValues ++ [value] } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter⟩ :=
      code_stack_after (value_types_concrete (baseValues ++ [value])) hc
    cases hop with
    | local_tee _ _ ty hi ht _ _ =>
      have hit : index < C.LOCALS.length := by simpa [labelContext, proj_uN_0] using hi
      simp only [labelContext, proj_uN_0, getElem!_pos C.LOCALS index hit] at ht
      have hlen : (baseValues.map valueType).length = front.length := by
        have hh := congrArg List.length hstack; simpa using hh
      have hvalue : valueType value = ty := by
        have hh := (List.append_inj (by simpa only [List.map_append, List.map_cons, List.map_nil] using hstack) hlen).2
        simpa only [List.cons.injEq, and_true] using hh
      have hv : Val_ok s value C.LOCALS[index] := by
        rw [ht, ← hvalue]
        exact results_typed_self_mem values (by simp)
      obtain ⟨types', locals', hw'⟩ := local_write_invariants localTypes locals hit hv hw
      apply FrameTyped.mk (f := { f with code := code, locals := f.locals.set index value, vals := baseValues ++ [value] }) C
        bindings types' locals' values returns ?_ hw'
      simpa only [List.append_nil, hstack] using hafter

/-- Completing an empty label exposes its already-typed continuation. -/
theorem code_stack_label_exit {C : context} {label : Label} {labels : List Label}
    {stack results : List valtype}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C (label :: labels) stack [] results) :
    CodeStackTyped C labels stack label.after results := by
  cases h with
  | @label _ _ saved operands _ _ height nesting code cont after =>
    have heq := concrete_empty
      (fun ty hty => concrete ty (List.mem_append_right saved hty)) code
    simpa only [heq] using after

theorem label_exit_frame_preservation {s : store} {f : AFrame}
    {label : Label} {labels : List Label}
    (h : FrameTyped s { f with labels := label :: labels, code := [] } []) :
    FrameTyped s { f with labels := labels, code := label.after } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    exact .mk C bindings localTypes locals values returns
      (by simpa only [List.append_nil] using code_stack_label_exit (value_types_concrete f.vals) hc) hw

/-- A suspended caller is typed with precisely the result values that a callee
may append on return. -/
theorem resume_frame_preservation {s : store} {f : AFrame}
    {incoming : List valtype} {values : List val}
    (h : FrameTyped s f incoming) (hv : ResultsTyped s incoming values) :
    FrameTyped s { f with vals := f.vals ++ values } [] := by
  cases h with
  | mk C bindings localTypes locals oldValues returns hc hw =>
    have htypes := results_type_of_typed hv
    apply FrameTyped.mk (f := { f with vals := f.vals ++ values }) C
      bindings localTypes locals ?_ returns ?_ hw
    · simpa only [ResultsTyped, List.map_append, htypes] using List.rel_append oldValues hv
    · simpa only [List.map_append, List.append_nil, htypes] using hc

/-- Updating only the active frame lifts its local preservation proof to the
whole call stack, provided its declared result types are unchanged. -/
theorem active_frame_preservation {s : store} {ambient : frame} {f f' : AFrame}
    {rest : List AFrame} {results : List val}
    (h : ATyped ⟨s, ambient, f :: rest, results⟩)
    (hf' : FrameTyped s f' []) (ht : f'.resultTypes = f.resultTypes) :
    ATyped ⟨s, ambient, f' :: rest, results⟩ := by
  obtain ⟨hs, functions, ha, frames, values, active, heights⟩ := h
  cases frames with
  | cons hf hr =>
    exact ⟨hs, functions, ha, .cons hf' (by simpa only [ht] using hr), values,
      (fun _ => active (by simp)), replace_frame_heights heights (frame_typed_heights hf')⟩

/-- Returning typed values either finishes execution or resumes the typed
caller. This lemma makes the caller's pending-result invariant explicit. -/
theorem return_values_preservation {s : store} {ambient : frame} {f : AFrame}
    {rest : List AFrame} {values : List val}
    (h : ATyped ⟨s, ambient, f :: rest, []⟩)
    (hv : ResultsTyped s f.resultTypes values) :
    match rest with
    | [] => ATyped ⟨s, ambient, [], values⟩
    | caller :: callers => ATyped ⟨s, ambient, { caller with vals := caller.vals ++ values } :: callers, []⟩ := by
  obtain ⟨hs, functions, ha, frames, _, _, heights⟩ := h
  cases frames with
  | cons hf hr =>
    cases rest with
    | nil => exact ⟨hs, functions, ha, .nil [], results_typed_wf hv, by simp, by simp [Forall]⟩
    | cons caller callers =>
      cases hr with
      | cons hc hrest =>
        exact ⟨hs, functions, ha, .cons (resume_frame_preservation hc hv) hrest,
          by simp [Forall], by simp,
          replace_frame_heights (f := caller) (fun frame hm => heights frame (by simp [hm]))
            (frame_typed_heights (resume_frame_preservation hc hv))⟩

theorem results_typed_drop {s : store} {before after : List valtype} {values : List val}
    (h : ResultsTyped s (before ++ after) values) :
    ResultsTyped s after (values.drop before.length) := by
  simpa only [ResultsTyped, List.drop_left] using List.forall₂_drop before.length h

/-- Explicit return selects a genuinely typed suffix, even through nested labels
and the stack-polymorphic discarded prefix of the generated return rule. -/
theorem return_suffix_typed {s : store} {f : AFrame} {code : List instr}
    (h : FrameTyped s { f with code := .RETURN :: code } []) :
    ResultsTyped s f.resultTypes (f.vals.drop (f.vals.length - f.resultTypes.length)) := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack⟩ := code_stack_head (value_types_concrete f.vals) hc
    cases hop with
    | «return» _ discarded results outputs hr _ _ =>
      have heq : results = f.resultTypes := by
        simpa only [labelContext, returns, Option.some.injEq, list.mk_list.injEq] using hr.symm
      subst results
      have hlen := congrArg List.length hstack
      simp only [List.length_map, List.length_append] at hlen
      have hoff : f.vals.length - f.resultTypes.length = (front ++ discarded).length := by
        simp only [List.length_append]
        omega
      rw [hoff]
      apply results_typed_drop
      simpa only [hstack, List.append_assoc] using values

/-- Falling off the outer frame's code has exactly the declared result vector. -/
theorem frame_end_typed {s : store} {f : AFrame}
    (h : FrameTyped s { f with labels := [], code := [] } []) :
    ResultsTyped s f.resultTypes f.vals := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    have heq := code_empty_shape (value_types_concrete f.vals) hc
    change f.vals.map valueType = f.resultTypes at heq
    simpa only [heq] using values

end Itasca.Runtime.SourceMachine
