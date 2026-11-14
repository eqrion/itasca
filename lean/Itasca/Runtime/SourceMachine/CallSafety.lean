import Itasca.Runtime.SourceMachine.Numeric.Transition
import Itasca.Runtime.SourceMachine.Measure

/-!
Sections, each formerly its own module: Progress, Preservation, ControlSafety, CallSafety.
-/

/-! ## Progress -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec

theorem const_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn) (number : iN)
    (h : FrameTyped s { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    have hi := code_stack_wf hc (.CONST (numtype_Inn ty) (.mk_num__0 ty number)) (by simp)
    cases hi with
    | instr_case_13 _ _ hn =>
      obtain ⟨bits, heq, hb⟩ := integer_num_inv hn
      cases number with
      | mk_uN n =>
        simp only [num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] at heq
        subst n
        cases ty <;>
          simp_all [astep, integer, integerWidth, numtype_Inn, advance]

theorem block_type_of_typing {C : context} {m : moduleinst} {bt : blocktype}
    {ft : functype} (types : C.TYPES = m.TYPES) (h : Blocktype_ok C bt ft) :
    blockType m bt = some ft := by
  cases h with
  | valtype opt _ _ => cases opt <;> rfl
  | typeidx index inputs outputs hi heq _ _ =>
    cases index with
    | mk_uN index =>
      simp only [proj_uN_0] at hi heq
      simp only [blockType, ← types, List.getElem?_eq_getElem hi]
      congr 1
      simpa only [getElem!_pos C.TYPES index hi] using heq

/-- Empty source code has equal input/output stacks once bottom types are
excluded by actual runtime values. -/
theorem concrete_empty {C : context} {actual expected : List valtype}
    (hc : Forall (fun ty => ty ≠ valtype.BOT) actual)
    (h : Instrs_ok C [] ⟨.mk_list actual, .mk_list expected⟩) : actual = expected :=
  concrete_result_sub_eq hc (Itasca.DeclarativeComplete.empty_sub h)

theorem value_types_concrete (values : List val) :
    Forall (fun ty => ty ≠ valtype.BOT) (values.map valueType) := by
  intro ty hty
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp hty
  exact value_type_ne_bot value

def EmptyShape (labels : List Label) (stack results : List valtype) : Prop :=
  match labels with
  | [] => stack = results
  | label :: _ => ∃ saved, stack = saved ++ label.resultTypes ∧ saved.length = label.height

theorem code_empty_shape {C : context} {labels : List Label}
    {stack results : List valtype}
    (concrete : Forall (fun ty => ty ≠ valtype.BOT) stack)
    (h : CodeStackTyped C labels stack [] results) :
    EmptyShape labels stack results := by
  cases h with
  | outer code => exact concrete_empty concrete code
  | @label label labels saved operands _ _ height nesting code cont after =>
    have hoperands : Forall (fun ty => ty ≠ valtype.BOT) operands :=
      fun ty hty => concrete ty (List.mem_append_right saved hty)
    have heq := concrete_empty hoperands code
    exact ⟨saved, by rw [heq], height⟩

/-- Every permitted local type has the zero/null default prescribed by Wasm. -/
theorem default_value_exists {ty : valtype} (h : ty ≠ .BOT) :
    ∃ value, defaultValue ty = some value := by
  cases ty <;> simp_all [defaultValue]

theorem default_locals_exists (types : List valtype)
    (h : Forall (fun ty => ty ≠ valtype.BOT) types) :
    ∃ values, defaultLocals (types.map local.LOCAL) = some values := by
  induction types with
  | nil => exact ⟨[], rfl⟩
  | cons ty types ih =>
    obtain ⟨value, hv⟩ := default_value_exists (h ty (by simp))
    obtain ⟨values, hs⟩ := ih (fun ty ht => h ty (by simp [ht]))
    exact ⟨value :: values, by simp [defaultLocals, hv, hs]⟩

theorem function_defaults {s : store} {fn : funcinst} {index : idx}
    {locals : List «local»} {body : expr} (hfunctions : FunctionsTyped s)
    (hmem : fn ∈ s.FUNCS) (hcode : fn.CODE = .FUNC index locals body) :
    ∃ values, defaultLocals locals = some values := by
  have h := hfunctions fn hmem
  simp only [hcode] at h
  obtain ⟨C, bindings, _, _, _, typed⟩ := h
  generalize hft : fn.TYPE = ft at typed
  cases typed with
  | mk_Func_ok _ types _ _ _ _ _ nonbot _ _ _ _ =>
    exact default_locals_exists types nonbot

end Itasca.Runtime.SourceMachine

end

/-! ## Preservation -/

section

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

end

/-! ## ControlSafety -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec Itasca.DeclarativeComplete

theorem instrs_prepend {C : context} {op : instr} {front inputs outputs results : List valtype}
    {after : List instr}
    (hop : Instr_ok C op ⟨.mk_list inputs, .mk_list outputs⟩) (hw : wf_instr op)
    (hafter : Instrs_ok C after ⟨.mk_list (front ++ outputs), .mk_list results⟩) :
    Instrs_ok C (op :: after) ⟨.mk_list (front ++ inputs), .mk_list results⟩ := by
  have hC := (wellFormed hafter).1
  have hone := Instrs_ok.instr C op inputs outputs hop hC hw
  have hframe := Instrs_ok.frame C [op] front inputs outputs hone hC (by simpa [Forall] using hw)
  exact append hframe hafter

/-- A primitive instruction can be restored before a typed continuation when
its operands lie above every saved label height. -/
theorem code_stack_prepend {C : context} {labels : List Label}
    {front inputs outputs results : List valtype} {op : instr} {after : List instr}
    (hop : Instr_ok (labelContext C labels) op ⟨.mk_list inputs, .mk_list outputs⟩)
    (hw : wf_instr op) (heights : ∀ label ∈ labels, label.height ≤ front.length)
    (h : CodeStackTyped C labels (front ++ outputs) after results) :
    CodeStackTyped C labels (front ++ inputs) (op :: after) results := by
  generalize heq : front ++ outputs = stack at h
  cases h with
  | outer code =>
    subst stack
    exact .outer (instrs_prepend hop hw code)
  | @label label labels saved operands _ _ height nesting code cont rest =>
    have hb : saved.length ≤ front.length := by rw [height]; exact heights label (by simp)
    have hsaved : front.take saved.length = saved := by
      have hh := congrArg (List.take saved.length) heq
      simpa only [List.take_append_of_le_length hb, List.take_left] using hh
    have hoperands : front.drop saved.length ++ outputs = operands := by
      have hh := congrArg (List.drop saved.length) heq
      simpa only [List.drop_append_of_le_length hb, List.drop_left] using hh
    have hcode : Instrs_ok (labelContext C (label :: labels)) (op :: after)
        ⟨.mk_list (front.drop saved.length ++ inputs), .mk_list label.resultTypes⟩ := by
      apply instrs_prepend hop hw
      simpa only [hoperands] using code
    have hfull := CodeStackTyped.label height nesting hcode cont rest
    have hsplit : saved ++ (front.drop saved.length ++ inputs) = front ++ inputs := by
      rw [← List.append_assoc]
      exact congrArg (fun xs => xs ++ inputs)
        ((congrArg (fun xs => xs ++ front.drop saved.length) hsaved.symm).trans
          (List.take_append_drop saved.length front))
    simpa only [hsplit] using hfull

theorem instrs_prepend_sequence {C : context} {before after : List instr}
    {front inputs outputs results : List valtype}
    (hbefore : Instrs_ok C before ⟨.mk_list inputs, .mk_list outputs⟩)
    (hafter : Instrs_ok C after ⟨.mk_list (front ++ outputs), .mk_list results⟩) :
    Instrs_ok C (before ++ after) ⟨.mk_list (front ++ inputs), .mk_list results⟩ :=
  append (.frame C before front inputs outputs hbefore (wellFormed hbefore).1 (wellFormed hbefore).2) hafter

theorem code_stack_prepend_sequence {C : context} {labels : List Label}
    {front inputs outputs results : List valtype} {before after : List instr}
    (hbefore : Instrs_ok (labelContext C labels) before ⟨.mk_list inputs, .mk_list outputs⟩)
    (heights : ∀ label ∈ labels, label.height ≤ front.length)
    (h : CodeStackTyped C labels (front ++ outputs) after results) :
    CodeStackTyped C labels (front ++ inputs) (before ++ after) results := by
  generalize heq : front ++ outputs = stack at h
  cases h with
  | outer code =>
    subst stack
    exact .outer (instrs_prepend_sequence hbefore code)
  | @label label labels saved operands _ _ height nesting code cont rest =>
    have hb : saved.length ≤ front.length := by rw [height]; exact heights label (by simp)
    have hsaved : front.take saved.length = saved := by
      have hh := congrArg (List.take saved.length) heq
      simpa only [List.take_append_of_le_length hb, List.take_left] using hh
    have hoperands : front.drop saved.length ++ outputs = operands := by
      have hh := congrArg (List.drop saved.length) heq
      simpa only [List.drop_append_of_le_length hb, List.drop_left] using hh
    have hcode : Instrs_ok (labelContext C (label :: labels)) (before ++ after)
        ⟨.mk_list (front.drop saved.length ++ inputs), .mk_list label.resultTypes⟩ := by
      apply instrs_prepend_sequence hbefore
      simpa only [hoperands] using code
    have hfull := CodeStackTyped.label height nesting hcode cont rest
    have hsplit : saved ++ (front.drop saved.length ++ inputs) = front ++ inputs := by
      rw [← List.append_assoc]
      exact congrArg (fun xs => xs ++ inputs)
        ((congrArg (fun xs => xs ++ front.drop saved.length) hsaved.symm).trans
          (List.take_append_drop saved.length front))
    simpa only [hsplit] using hfull

/-- The typed continuation for any branch target can be recovered by unwinding
the explicit labels; the saved prefix is the current stack below its height. -/
theorem code_stack_branch_target {C : context} {labels : List Label}
    {stack results : List valtype} {code : List instr}
    (h : CodeStackTyped C labels stack code results)
    (depth : Nat) (target : Label) (lookup : labels[depth]? = some target) :
    CodeStackTyped C (labels.drop (depth + 1))
      (stack.take target.height ++ target.branchTypes) (target.cont ++ target.after) results := by
  induction h generalizing depth target with
  | outer hc => simp at lookup
  | @label label labels saved operands code results height nesting hc cont after ih =>
    cases depth with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst target
      have hh := code_stack_prepend_sequence cont
        (fun outer ho => by rw [height]; exact nesting outer ho) after
      simpa only [List.drop_succ_cons, List.drop_zero, ← height, List.take_left] using hh
    | succ depth =>
      simp only [List.getElem?_cons_succ] at lookup
      have hh := ih depth target lookup
      have hb : target.height ≤ saved.length := by
        rw [height]
        exact nesting target (List.mem_of_getElem? lookup)
      simpa only [List.drop_succ_cons, List.take_append_of_le_length hb] using hh

/-- Entering a block transfers its generated body derivation to a new typed
label and retains the already-typed outer continuation. -/
theorem block_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BLOCK bt body :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, inputs, outputs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | block _ _ _ ins outs hbt hbody hC hi hnew =>
        have hbt' := block_type_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - inputs.length = front.length := by omega
        have hbound : inputs.length ≤ f.vals.length := by omega
        have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
          rw [List.map_drop, hstack, hheight, List.drop_left]
        let label : Label := ⟨outputs, outputs, [], front.length, after⟩
        let frame' : AFrame := { f with labels := label :: f.labels, code := body }
        have hcode : CodeStackTyped C (label :: f.labels) (f.vals.map valueType) body f.resultTypes := by
          rw [hstack]
          apply CodeStackTyped.label (saved := front) (operands := inputs) rfl heights ?_ ?_ hafter
          · exact hbody
          · exact empty_iff.mpr ⟨hC, result_sub_refl outputs⟩
        have hf' : FrameTyped s frame' [] :=
          .mk C bindings localTypes locals values returns (by simpa [frame'] using hcode) hw
        have hnext : next = ⟨s, ambient, frame' :: rest, []⟩ := by
          simpa [astep, enterLabel, hbt', hbound, htail, hheight, hstack, advance, label, frame'] using step.symm
        rw [hnext]
        exact active_frame_preservation typed hf' rfl

/-- Entering a loop transfers its generated body derivation to a new typed
label and retains the already-typed outer continuation. -/
theorem loop_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (bt : blocktype) (body : List instr)
    (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .LOOP bt body :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, inputs, outputs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      have original := hop
      cases hop with
      | loop _ _ _ ins outs hbt hbody hC hi hnew =>
        have hbt' := block_type_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - inputs.length = front.length := by omega
        have hbound : inputs.length ≤ f.vals.length := by omega
        have htail : (f.vals.drop (f.vals.length - inputs.length)).map valueType = inputs := by
          rw [List.map_drop, hstack, hheight, List.drop_left]
        let label : Label := ⟨inputs, outputs, [.LOOP bt body], front.length, after⟩
        let frame' : AFrame := { f with labels := label :: f.labels, code := body }
        have hcode : CodeStackTyped C (label :: f.labels) (f.vals.map valueType) body f.resultTypes := by
          rw [hstack]
          apply CodeStackTyped.label (saved := front) (operands := inputs) rfl heights ?_ ?_ hafter
          · exact hbody
          · exact Instrs_ok.instr _ _ _ _ original hC hi
        have hf' : FrameTyped s frame' [] :=
          .mk C bindings localTypes locals values returns (by simpa [frame'] using hcode) hw
        have hnext : next = ⟨s, ambient, frame' :: rest, []⟩ := by
          simpa [astep, enterLabel, hbt', hbound, htail, hheight, hstack, advance, label, frame'] using step.symm
        rw [hnext]
        exact active_frame_preservation typed hf' rfl

/-- Selecting an if arm replaces it by the corresponding typed block and
consumes only the i32 condition. -/
theorem if_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {baseValues : List val} {bits : Nat} {bt : blocktype} {yes no : List instr}
    (h : FrameTyped s { f with code := .IFELSE bt yes no :: after, vals := baseValues ++ [integerVal .I32 bits] } []) :
    FrameTyped s { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := baseValues } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
      code_stack_after_bounds (value_types_concrete (baseValues ++ [integerVal .I32 bits])) hc
    cases hop with
    | «if» _ _ _ _ inputs outputs hbt hyes hno hC hi hnew =>
      have hbase : baseValues.map valueType = front ++ inputs := by
        simpa only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
          numtype_Inn, valtype_numtype, ← List.append_assoc, List.append_cancel_right_eq] using hstack
      have hbody : Instrs_ok { labelContext C f.labels with LABELS := .mk_list outs :: (labelContext C f.labels).LABELS } (if bits = 0 then no else yes)
          ⟨.mk_list inputs, .mk_list outs⟩ := by
        split <;> assumption
      have hblock : wf_instr (.BLOCK bt (if bits = 0 then no else yes)) := by
        cases hi with
        | instr_case_6 _ _ _ hbt hy hn =>
          apply wf_instr.instr_case_4 _ _ hbt
          split <;> assumption
      have hop' := Instr_ok.block (labelContext C f.labels) bt (if bits = 0 then no else yes)
        inputs outs hbt hbody hC hblock hnew
      have hcode := code_stack_prepend hop' hblock heights hafter
      have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
        simpa using results_typed_take baseValues.length values
      exact FrameTyped.mk (f := { f with code := .BLOCK bt (if bits = 0 then no else yes) :: after, vals := baseValues }) C bindings localTypes locals hvalues returns
        (by simpa only [List.append_nil, hbase] using hcode) hw

/-- Conditional branching either removes its condition or replaces itself by
the generated unconditional branch rule with the same required label values. -/
theorem br_if_frame_preservation {s : store} {f : AFrame} {after : List instr}
    {baseValues : List val} {bits : Nat} {depth : idx}
    (h : FrameTyped s { f with code := .BR_IF depth :: after, vals := baseValues ++ [integerVal .I32 bits] } []) :
    FrameTyped s { f with code := if bits = 0 then after else .BR depth :: after, vals := baseValues } [] := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
      code_stack_after_bounds (value_types_concrete (baseValues ++ [integerVal .I32 bits])) hc
    cases hop with
    | br_if _ _ types hi ht hC hinst =>
      have hbase : baseValues.map valueType = front ++ outs := by
        simpa only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
          numtype_Inn, valtype_numtype, ← List.append_assoc, List.append_cancel_right_eq] using hstack
      have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
        simpa using results_typed_take baseValues.length values
      apply FrameTyped.mk (f := { f with code := if bits = 0 then after else .BR depth :: after, vals := baseValues }) C bindings localTypes locals hvalues returns ?_ hw
      by_cases hz : bits = 0
      · simpa only [hz, ↓reduceIte, List.append_nil, hbase] using hafter
      · have hbr : wf_instr (.BR depth) := by
          cases hinst with | instr_case_8 _ hidx => exact .instr_case_7 _ hidx
        have hop' : Instr_ok (labelContext C f.labels) (.BR depth) ⟨.mk_list outs, .mk_list outs⟩ := by
          simpa using Instr_ok.br (labelContext C f.labels) depth [] outs outs hi ht hC hbr
        simpa only [hz, ↓reduceIte, List.append_nil, hbase] using code_stack_prepend hop' hbr heights hafter

/-- Branching preserves the recovered target continuation and carries exactly
its typed result suffix over the saved prefix below the target height. -/
theorem br_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (depth : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack⟩ := code_stack_head (value_types_concrete f.vals) hc
      cases hop with
      | br _ _ discarded types outputs hi ht _ _ =>
        have hi' : depth < f.labels.length := by simpa [labelContext, proj_uN_0] using hi
        let target := f.labels[depth]
        have lookup : f.labels[depth]? = some target := List.getElem?_eq_getElem hi'
        have htypes : target.branchTypes = types := by
          simpa [target, labelContext, proj_uN_0, proj_list_0, getElem!_pos, hi'] using ht
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hoff : f.vals.length - target.arity = (front ++ discarded).length := by
          simp only [Label.arity, htypes, List.length_append]
          omega
        have hsuffix : ResultsTyped s target.branchTypes (f.vals.drop (f.vals.length - target.arity)) := by
          rw [htypes, hoff]
          apply results_typed_drop
          simpa only [hstack, List.append_assoc] using values
        have hsuffixTypes := results_type_of_typed hsuffix
        have hpref := results_typed_take target.height values
        let frame' : AFrame := { f with vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity), labels := f.labels.drop (depth + 1), code := target.cont ++ target.after }
        have hf' : FrameTyped s frame' [] := by
          apply FrameTyped.mk (f := frame') C bindings localTypes locals ?_ returns ?_ hw
          · simpa only [frame', ResultsTyped, List.map_append, hsuffixTypes] using List.rel_append hpref hsuffix
          · simpa only [frame', List.append_nil, List.map_append, List.map_take, hsuffixTypes] using
              code_stack_branch_target hc depth target lookup
        simp only [astep, branch, lookup] at step
        split at step
        · have heq : next = ⟨s, ambient, frame' :: rest, []⟩ := by
            simpa only [advance, AResult.next.injEq, frame'] using step.symm
          rw [heq]
          exact active_frame_preservation typed hf' rfl
        · contradiction

end Itasca.Runtime.SourceMachine

end

/-! ## CallSafety -/

section

namespace Itasca.Runtime.SourceMachine
open SpecExt Itasca.Runtime.Spec Itasca.DeclarativeComplete

theorem zero_float_wf (ty : Fnn) :
    wf_val (.CONST (numtype_Fnn ty) (.mk_num__1 ty (.POS (.SUBNORM 0)))) := by
  apply wf_val.val_case_0
  apply wf_num_.num__case_1 _ _ _ ?_ rfl
  apply wf_fN.fN_case_0
  exact wf_fNmag.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩

/-- Zero/null local defaults inhabit their exact declared Wasm value type. -/
theorem default_value_typed {s : store} (hs : wf_store s) (ty : valtype)
    (ht : ty ≠ .BOT) :
    ∃ value, defaultValue ty = some value ∧ Val_ok s value ty := by
  cases ty with
  | I32 => exact ⟨_, rfl, integer_val_typed hs .I32 0 (by decide)⟩
  | I64 => exact ⟨_, rfl, integer_val_typed hs .I64 0 (by decide)⟩
  | F32 => exact ⟨_, rfl, .numtype _ _ _ hs (zero_float_wf .F32)⟩
  | F64 => exact ⟨_, rfl, .numtype _ _ _ hs (zero_float_wf .F64)⟩
  | V128 =>
    refine ⟨_, rfl, Val_ok.vectype _ _ _ hs ?_⟩
    exact .val_case_1 _ _ (by decide) (.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩)
  | FUNCREF => exact ⟨_, rfl, .reftype _ _ _ (.null _ _ hs) hs⟩
  | EXTERNREF => exact ⟨_, rfl, .reftype _ _ _ (.null _ _ hs) hs⟩
  | BOT => contradiction

theorem default_locals_typed {s : store} (hs : wf_store s) (types : List valtype)
    (h : Forall (fun ty => ty ≠ valtype.BOT) types) :
    ∃ values, defaultLocals (types.map local.LOCAL) = some values ∧ ResultsTyped s types values := by
  induction types with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ty types ih =>
    obtain ⟨value, hv, hvt⟩ := default_value_typed hs ty (h ty (by simp))
    obtain ⟨values, hs, hvs⟩ := ih (fun ty ht => h ty (by simp [ht]))
    exact ⟨value :: values, by simp [defaultLocals, hv, hs], .cons hvt hvs⟩

theorem wf_context_scope {C : context} (h : wf_context C)
    (locals : List valtype) (labels : List resulttype) (returns : Option resulttype) :
    wf_context { C with LOCALS := locals, LABELS := labels, RETURN := returns } := by
  cases h
  constructor <;> assumption

theorem ModuleBindings.scope {s : store} {m : moduleinst} {C : context}
    (h : ModuleBindings s m C) (locals : List valtype)
    (labels : List resulttype) (returns : Option resulttype) :
    ModuleBindings s m { C with LOCALS := locals, LABELS := labels, RETURN := returns } :=
  ⟨h.types, h.funcs, h.globals, h.tables, h.mems, h.elems, h.datas,
    wf_context_scope h.wf locals labels returns⟩

theorem function_module_wf {s : store} (h : wf_store s)
    {fn : funcinst} (hm : fn ∈ s.FUNCS) : wf_moduleinst fn.MODULE := by
  cases h with
  | store_case_ _ _ _ _ _ _ funcs _ _ _ _ =>
    have hf := funcs fn hm
    cases hf
    assumption

/-- The generated function rule installs precisely the parameters, declared
locals, result label, and return type used by the abstract callee. -/
theorem callee_frame_typed {s : store} {m : moduleinst} {C : context}
    {index : idx} {locals : List «local»} {body : List instr}
    {params results : List valtype} {args : List val}
    (hs : wf_store s) (hm : wf_moduleinst m) (bindings : ModuleBindings s m C)
    (hl : C.LOCALS = []) (hb : C.LABELS = [])
    (hf : Func_ok C (.FUNC index locals body) ⟨.mk_list params, .mk_list results⟩)
    (ha : ResultsTyped s params args) (address : funcaddr) :
    ∃ defaults, defaultLocals locals = some defaults ∧
      FrameTyped s ⟨address, results, args ++ defaults, m,
        [⟨results, results, [], 0, []⟩], body, []⟩ [] := by
  cases hf with
  | mk_Func_ok _ types _ _ _ _ _ nonbot expression _ _ _ =>
    obtain ⟨defaults, hd, hdt⟩ := default_locals_typed hs types nonbot
    refine ⟨defaults, hd, ?_⟩
    let C' : context := { C with LOCALS := params ++ types, LABELS := [], RETURN := some (.mk_list results) }
    have hv : ResultsTyped s (params ++ types) (args ++ defaults) := List.rel_append ha hdt
    have hmap := results_type_of_typed hv
    have hw : wf_context (labelContext C' []) := wf_context_scope bindings.wf _ _ _
    apply FrameTyped.mk (f := ⟨address, results, args ++ defaults, m, [⟨results, results, [], 0, []⟩], body, []⟩) C' (bindings.scope _ _ _) hmap.symm hv (.nil) rfl ?_
      (.frame_case_ _ _ (results_typed_wf hv) hm)
    apply CodeStackTyped.label (saved := []) (operands := []) rfl (by simp) ?_ ?_ ?_
    · cases expression with
      | mk_Expr_ok _ code _ _ =>
        change Instrs_ok (append_context _ C) body _ at code
        simpa [labelContext, C', append_context, hl, hb] using code
    · exact empty_iff.mpr ⟨hw, result_sub_refl results⟩
    · exact .outer (empty_iff.mpr ⟨hw, result_sub_refl results⟩)

/-- A defined call preserves both the newly installed callee and its suspended
caller. The declaration and address are resolved from actual module bindings. -/
theorem call_preservation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩ = .next next) :
    ATyped next := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        code_stack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht _ _ =>
        simp only [labelContext, proj_uN_0] at hi ht
        have hi' : index < f.module.FUNCS.length := by
          rw [bindings.funcs.length_eq]
          exact hi
        obtain ⟨fn, hfn, htype⟩ := bindings.funcs.get hi' hi
        simp only [List.get_eq_getElem] at hfn htype
        have htype' : fn.TYPE = ⟨.mk_list ins, .mk_list outs⟩ := by
          rw [htype]
          simpa only [getElem!_pos C.FUNCS index hi] using ht
        have hresolve := List.getElem?_eq_getElem hi'
        have hlen := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hlen
        have hheight : f.vals.length - ins.length = front.length := by omega
        have hbound : ins.length ≤ f.vals.length := by omega
        have hargs : ResultsTyped s ins (f.vals.drop front.length) := by
          apply results_typed_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hfront : (f.vals.take front.length).map valueType = front := by
          rw [List.map_take, hstack, List.take_left]
        have hcaller : FrameTyped s { f with vals := f.vals.take front.length, code := after } outs := by
          apply FrameTyped.mk (f := { f with vals := f.vals.take front.length, code := after }) C
            bindings localTypes locals (results_typed_take front.length values) returns ?_ hw
          simpa only [hfront] using hafter
        have hcallerHeights : FrameHeights { f with vals := f.vals.take front.length, code := after } := by
          intro label hm
          have hh := heights label hm
          simp only [List.length_take]
          omega
        cases hcode : fn.CODE with
        | HOST host =>
          simp [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode] at step
        | FUNC fi fl body =>
          have htyped := typed.functions fn (List.mem_of_getElem? hfn)
          simp only [hcode] at htyped
          obtain ⟨Cfn, hbindings, hlocals, hlabels, _, hfunc⟩ := htyped
          rw [htype'] at hfunc
          obtain ⟨defaults, hdefaults, hcallee⟩ := callee_frame_typed typed.store
            (function_module_wf typed.store (List.mem_of_getElem? hfn)) hbindings hlocals hlabels hfunc hargs
            (f.module.FUNCS[index])
          have hnext : next = ⟨s, ambient,
              ⟨f.module.FUNCS[index], outs, f.vals.drop front.length ++ defaults, fn.MODULE,
                [⟨outs, outs, [], 0, []⟩], body, []⟩ ::
              { f with vals := f.vals.take front.length, code := after } :: rest, []⟩ := by
            simpa [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode, hdefaults] using step.symm
          rw [hnext]
          refine ⟨typed.store, typed.functions, typed.ambient, .cons hcallee (.cons hcaller hr),
            by simp [Forall], by simp, ?_⟩
          intro frame hm
          simp only [List.mem_cons] at hm
          rcases hm with rfl | rfl | hm
          · exact frame_typed_heights hcallee
          · exact hcallerHeights
          · exact typed.heights frame (by simp [hm])

end Itasca.Runtime.SourceMachine

end
