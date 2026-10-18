import Exec.Abs.Preservation

namespace Exec.Abs
open SpecExt Exec.Spec Itasca.DeclarativeComplete

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
theorem codeStack_prepend {C : context} {labels : List Label}
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

theorem codeStack_prepend_sequence {C : context} {labels : List Label}
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
theorem codeStack_branch_target {C : context} {labels : List Label}
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
      have hh := codeStack_prepend_sequence cont
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
        codeStack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | block _ _ _ ins outs hbt hbody hC hi hnew =>
        have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
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
        codeStack_after_bounds (value_types_concrete f.vals) hc
      have original := hop
      cases hop with
      | loop _ _ _ ins outs hbt hbody hC hi hnew =>
        have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
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
      codeStack_after_bounds (value_types_concrete (baseValues ++ [integerVal .I32 bits])) hc
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
      have hcode := codeStack_prepend hop' hblock heights hafter
      have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
        simpa using resultsTyped_take baseValues.length values
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
      codeStack_after_bounds (value_types_concrete (baseValues ++ [integerVal .I32 bits])) hc
    cases hop with
    | br_if _ _ types hi ht hC hinst =>
      have hbase : baseValues.map valueType = front ++ outs := by
        simpa only [List.map_append, List.map_cons, List.map_nil, integerVal, valueType,
          numtype_Inn, valtype_numtype, ← List.append_assoc, List.append_cancel_right_eq] using hstack
      have hvalues : ResultsTyped s (baseValues.map valueType) baseValues := by
        simpa using resultsTyped_take baseValues.length values
      apply FrameTyped.mk (f := { f with code := if bits = 0 then after else .BR depth :: after, vals := baseValues }) C bindings localTypes locals hvalues returns ?_ hw
      by_cases hz : bits = 0
      · simpa only [hz, ↓reduceIte, List.append_nil, hbase] using hafter
      · have hbr : wf_instr (.BR depth) := by
          cases hinst with | instr_case_8 _ hidx => exact .instr_case_7 _ hidx
        have hop' : Instr_ok (labelContext C f.labels) (.BR depth) ⟨.mk_list outs, .mk_list outs⟩ := by
          simpa using Instr_ok.br (labelContext C f.labels) depth [] outs outs hi ht hC hbr
        simpa only [hz, ↓reduceIte, List.append_nil, hbase] using codeStack_prepend hop' hbr heights hafter

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
      obtain ⟨front, ins, outs, hop, hstack⟩ := codeStack_head (value_types_concrete f.vals) hc
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
          apply resultsTyped_drop
          simpa only [hstack, List.append_assoc] using values
        have hsuffixTypes := results_type_of_typed hsuffix
        have hpref := resultsTyped_take target.height values
        let frame' : AFrame := { f with vals := f.vals.take target.height ++ f.vals.drop (f.vals.length - target.arity), labels := f.labels.drop (depth + 1), code := target.cont ++ target.after }
        have hf' : FrameTyped s frame' [] := by
          apply FrameTyped.mk (f := frame') C bindings localTypes locals ?_ returns ?_ hw
          · simpa only [frame', ResultsTyped, List.map_append, hsuffixTypes] using List.rel_append hpref hsuffix
          · simpa only [frame', List.append_nil, List.map_append, List.map_take, hsuffixTypes] using
              codeStack_branch_target hc depth target lookup
        simp only [astep, branch, lookup] at step
        split at step
        · have heq : next = ⟨s, ambient, frame' :: rest, []⟩ := by
            simpa only [advance, AResult.next.injEq, frame'] using step.symm
          rw [heq]
          exact active_frame_preservation typed hf' rfl
        · contradiction

end Exec.Abs
