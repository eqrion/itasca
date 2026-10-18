import Exec.Abs.Numeric.Astep
import Exec.Abs.Safety
import Exec.Abs.Slice

namespace Exec.Abs
open SpecExt Exec.Spec

/-- Source typing rules guarantee two real, correctly sized operands for add. -/
theorem add_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn)
    (h : FrameTyped s { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .ADD) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  cases hoperands with
  | cons hl hr =>
    cases hr with
    | cons hr hend =>
      cases hend
      obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
      obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
      cases ty <;>
        simp_all [astep, pop, integerVal, integer, integerBinary, integerWidth,
          numtype_Inn, advance, List.reverse_append]

theorem sub_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn)
    (h : FrameTyped s { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .BINOP (numtype_Inn ty) (.mk_binop__0 ty .SUB) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  cases hoperands with
  | cons hl hr =>
    cases hr with
    | cons hr hend =>
      cases hend
      obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
      obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
      cases ty <;>
        simp_all [astep, pop, integerVal, integer, integerBinary, integerWidth,
          numtype_Inn, advance, List.reverse_append]

/-- A typed drop always has an operand, even if its derivation used framing. -/
theorem drop_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr)
    (h : FrameTyped s { f with code := .DROP :: code } []) :
    astep ⟨s, ambient, { f with code := .DROP :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  cases hoperands with
  | cons hv hend =>
    cases hend
    simp [astep, hsplit, pop_append, advance]

theorem eqz_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn)
    (h : FrameTyped s { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .TESTOP (numtype_Inn ty) (.mk_testop__0 ty .EQZ) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  cases hoperands with
  | cons hv hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv hv
    cases ty <;>
      simp_all [astep, pop, integerVal, integer, integerWidth,
        numtype_Inn, advance, List.reverse_append]

theorem relation_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn) (op : relop_Inn)
    (hop : op = .EQ ∨ op = .LT .U)
    (h : FrameTyped s { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .RELOP (numtype_Inn ty) (.mk_relop__0 ty op) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, typed, hsplit, hoperands⟩ := frame_typed_operands h
  cases typed
  cases hoperands with
  | cons hl hr =>
    cases hr with
    | cons hr hend =>
      cases hend
      obtain ⟨a, rfl, ha⟩ := integer_val_inv hl
      obtain ⟨b, rfl, hb⟩ := integer_val_inv hr
      rcases hop with rfl | rfl <;> cases ty <;>
        simp_all [astep, pop, integerVal, integer, integerWidth,
          numtype_Inn, advance, List.reverse_append]

theorem const_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (ty : Inn) (number : iN)
    (h : FrameTyped s { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .CONST (numtype_Inn ty) (.mk_num__0 ty number) :: code } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    have hi := codeStack_wf hc (.CONST (numtype_Inn ty) (.mk_num__0 ty number)) (by simp)
    cases hi with
    | instr_case_13 _ _ hn =>
      obtain ⟨bits, heq, hb⟩ := integer_num_inv hn
      cases number with
      | mk_uN n =>
        simp only [num_.mk_num__0.injEq, uN.mk_uN.injEq, true_and] at heq
        subst n
        cases ty <;>
          simp_all [astep, integer, integerWidth, numtype_Inn, advance]

theorem local_get_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (index : Nat)
    (h : FrameTyped s { f with code := .LOCAL_GET (.mk_uN index) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .LOCAL_GET (.mk_uN index) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, hlocals, hop, _, _⟩ := frame_typed_operands h
  cases hop with
  | local_get _ _ _ hi ht _ _ =>
    have hi' : index < f.locals.length := by simpa [labelContext, hlocals, proj_uN_0] using hi
    simp [astep, List.getElem?_eq_getElem hi', advance]

theorem local_set_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (index : Nat)
    (h : FrameTyped s { f with code := .LOCAL_SET (.mk_uN index) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .LOCAL_SET (.mk_uN index) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, hlocals, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop with
  | local_set _ _ ty hi ht _ _ =>
    have hi' : index < f.locals.length := by simpa [labelContext, hlocals, proj_uN_0] using hi
    have oldType : valueType f.locals[index] = ty := by
      simpa [labelContext, hlocals, proj_uN_0, getElem!_pos, hi'] using ht
    cases hoperands with
    | cons hv hend =>
      cases hend
      have newType := value_type_of_typed hv
      simp [astep, hsplit, pop_append, List.getElem?_eq_getElem hi',
        newType, oldType, advance]

theorem local_tee_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (index : Nat)
    (h : FrameTyped s { f with code := .LOCAL_TEE (.mk_uN index) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .LOCAL_TEE (.mk_uN index) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, hlocals, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop with
  | local_tee _ _ ty hi ht _ _ =>
    have hi' : index < f.locals.length := by simpa [labelContext, hlocals, proj_uN_0] using hi
    have oldType : valueType f.locals[index] = ty := by
      simpa [labelContext, hlocals, proj_uN_0, getElem!_pos, hi'] using ht
    cases hoperands with
    | cons hv hend =>
      cases hend
      have newType := value_type_of_typed hv
      simp [astep, hsplit, pop_append, List.getElem?_eq_getElem hi',
        newType, oldType, advance]

theorem br_if_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (depth : Nat)
    (h : FrameTyped s { f with code := .BR_IF (.mk_uN depth) :: code } []) :
    astep ⟨s, ambient,
      { f with code := .BR_IF (.mk_uN depth) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  obtain ⟨args, conditions, rfl, _, hcond⟩ := resultsTyped_split hoperands
  cases hcond with
  | cons hvalue hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
    norm_num [integerWidth] at hb
    simp [astep, hsplit, List.append_assoc, pop, integerVal, integer, numtype_Inn,
      integerWidth, advance, hb] 

theorem if_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (bt : blocktype) (yes no : List instr)
    (h : FrameTyped s { f with code := .IFELSE bt yes no :: code } []) :
    astep ⟨s, ambient,
      { f with code := .IFELSE bt yes no :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, _, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop
  obtain ⟨args, conditions, rfl, _, hcond⟩ := resultsTyped_split hoperands
  cases hcond with
  | cons hvalue hend =>
    cases hend
    obtain ⟨bits, rfl, hb⟩ := integer_val_inv (ty := .I32) hvalue
    norm_num [integerWidth] at hb
    simp [astep, hsplit, List.append_assoc, pop, integerVal, integer, numtype_Inn,
      integerWidth, advance, hb]

theorem blockType_of_typing {C : context} {m : moduleinst} {bt : blocktype}
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

theorem block_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (bt : blocktype) (body : List instr)
    (h : FrameTyped s { f with code := .BLOCK bt body :: code } []) :
    astep ⟨s, ambient,
      { f with code := .BLOCK bt body :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, bindings, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop with
  | block _ _ _ inputs outputs hbt _ _ _ _ =>
    have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
    have hlen := resultsTyped_length hoperands
    have htypes := results_type_of_typed hoperands
    simp [astep, enterLabel, hbt', hsplit, ← hlen, htypes, advance]

theorem loop_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (bt : blocktype) (body : List instr)
    (h : FrameTyped s { f with code := .LOOP bt body :: code } []) :
    astep ⟨s, ambient,
      { f with code := .LOOP bt body :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, bindings, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
  cases hop with
  | loop _ _ _ inputs outputs hbt _ _ _ _ =>
    have hbt' := blockType_of_typing (m := f.module) (C := labelContext C f.labels) bindings.types hbt
    have hlen := resultsTyped_length hoperands
    have htypes := results_type_of_typed hoperands
    simp [astep, enterLabel, hbt', hsplit, ← hlen, htypes, advance]

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
  exact valueType_ne_bot value

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

/-- Finishing a label or frame cannot fail its dynamic result check. -/
theorem empty_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (h : FrameTyped s { f with code := [] } []) :
    astep ⟨s, ambient, { f with code := [] } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    have shape := code_empty_shape (value_types_concrete f.vals) hc
    cases hl : f.labels with
    | nil =>
      simp only [hl, EmptyShape] at shape
      have hlen := congrArg List.length shape
      simp only [List.length_map] at hlen
      simp only [astep, hl, returnFrame, AFrame.arity]
      have htail : (f.vals.drop (f.vals.length - f.resultTypes.length)).map valueType = f.resultTypes := by
        simp [hlen, shape]
      simp only [hlen, Nat.le_refl, htail, and_self, ↓reduceIte]
      cases rest <;> simp [advance, shape]
    | cons label labels =>
      simp only [hl, EmptyShape] at shape
      obtain ⟨saved, heq, height⟩ := shape
      have hstack : f.vals.length = label.height + label.resultTypes.length := by
        have h := congrArg List.length heq
        simpa only [List.length_map, List.length_append, height] using h
      have htail : (f.vals.drop label.height).map valueType = label.resultTypes := by
        rw [List.map_drop, heq, ← height, List.drop_left]
      simp [astep, hl, hstack, htail, advance]

/-- An explicit return obtains its suffix type from the enclosing function's
RETURN context, independently of intervening labels. -/
theorem return_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr)
    (h : FrameTyped s { f with code := .RETURN :: code } []) :
    astep ⟨s, ambient, { f with code := .RETURN :: code } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack⟩ := codeStack_head (value_types_concrete f.vals) hc
    cases hop with
    | «return» _ discarded results outputs hr _ _ =>
      have heq : results = f.resultTypes := by
        simpa only [labelContext, returns, Option.some.injEq, list.mk_list.injEq] using hr.symm
      subst results
      have hlen : f.resultTypes.length ≤ f.vals.length := by
        have hh := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hh
        omega
      have htail : (f.vals.drop (f.vals.length - f.resultTypes.length)).map valueType = f.resultTypes := by
        rw [List.map_drop, hstack]
        have hh := congrArg List.length hstack
        simp only [List.length_map, List.length_append] at hh
        rw [← List.append_assoc]
        have hn : f.vals.length - f.resultTypes.length = (front ++ discarded).length := by
          simp only [List.length_append]
          omega
        rw [hn, List.drop_left]
      simp only [astep, returnFrame, AFrame.arity, hlen, htail, and_self, ↓reduceIte]
      cases rest <;> simp [advance]

/-- Every permitted local type has the zero/null default prescribed by Wasm. -/
theorem defaultValue_exists {ty : valtype} (h : ty ≠ .BOT) :
    ∃ value, defaultValue ty = some value := by
  cases ty <;> simp_all [defaultValue]

theorem defaultLocals_exists (types : List valtype)
    (h : Forall (fun ty => ty ≠ valtype.BOT) types) :
    ∃ values, defaultLocals (types.map local.LOCAL) = some values := by
  induction types with
  | nil => exact ⟨[], rfl⟩
  | cons ty types ih =>
    obtain ⟨value, hv⟩ := defaultValue_exists (h ty (by simp))
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
    exact defaultLocals_exists types nonbot

/-- Actual module bindings resolve the generated call type to an existing
function instance before the operand suffix and defaults are checked. -/
theorem call_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (index : Nat)
    (functions : FunctionsTyped s)
    (h : FrameTyped s { f with code := .CALL (.mk_uN index) :: code } []) :
    astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: code } :: rest, []⟩ ≠ .stuck := by
  obtain ⟨C, first, operands, ins, outs, bindings, _, hop, hsplit, hoperands⟩ := frame_typed_operands h
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
    have hresolve : f.module.FUNCS[index]? = some (f.module.FUNCS[index]) :=
      List.getElem?_eq_getElem hi'
    have htypes := results_type_of_typed hoperands
    have hlen := resultsTyped_length hoperands
    cases hcode : fn.CODE with
    | HOST host =>
      simp [astep, call, hresolve, hfn, htype', hsplit, ← hlen, htypes, hcode]
    | FUNC index locals body =>
      obtain ⟨defaults, hdefaults⟩ := function_defaults functions
        (List.mem_of_getElem? hfn) hcode
      simp [astep, call, hresolve, hfn, htype', hsplit, ← hlen, htypes, hcode, hdefaults]

/-- A branch's target exists and its saved stack lies below the required result
suffix; both facts follow from generated branch typing and label nesting. -/
theorem br_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (code : List instr) (depth : Nat)
    (h : FrameTyped s { f with code := .BR (.mk_uN depth) :: code } []) :
    astep ⟨s, ambient, { f with code := .BR (.mk_uN depth) :: code } :: rest, []⟩ ≠ .stuck := by
  cases h with
  | mk C bindings localTypes locals values returns hc hw =>
    simp only [List.append_nil] at hc
    obtain ⟨front, ins, outs, hop, hstack, heights⟩ :=
      codeStack_head_bounds (value_types_concrete f.vals) hc
    cases hop with
    | br _ _ discarded types outputs hi ht _ _ =>
      have hi' : depth < f.labels.length := by simpa [labelContext, proj_uN_0] using hi
      have htypes : f.labels[depth].branchTypes = types := by
        simpa [labelContext, proj_uN_0, proj_list_0, getElem!_pos, hi'] using ht
      have hheight := heights f.labels[depth] (List.getElem_mem hi')
      have hlen := congrArg List.length hstack
      simp only [List.length_map, List.length_append] at hlen
      have hbound : f.labels[depth].height + f.labels[depth].arity ≤ f.vals.length := by
        simp only [Label.arity, htypes]
        omega
      have htail : (f.vals.drop (f.vals.length - f.labels[depth].arity)).map valueType = f.labels[depth].branchTypes := by
        rw [List.map_drop, hstack, Label.arity, htypes, ← List.append_assoc]
        have hn : f.vals.length - types.length = (front ++ discarded).length := by
          simp only [List.length_append]
          omega
        rw [hn, List.drop_left]
      simp [astep, branch, List.getElem?_eq_getElem hi', hbound, htail, advance]

/-- The complete integer slice cannot get stuck in a source-typed active frame.
This statement includes label completion, function return, and actual calls. -/
theorem frame_progress (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (functions : FunctionsTyped s)
    (typed : FrameTyped s f []) (slice : Forall SliceInstr f.code) :
    astep ⟨s, ambient, f :: rest, []⟩ ≠ .stuck := by
  cases f with
  | mk addr rts locals m labels code values =>
    let f : AFrame := ⟨addr, rts, locals, m, labels, code, values⟩
    cases code with
    | nil => exact empty_progress s ambient f rest typed
    | cons op after =>
      have hop := slice op (by simp)
      cases hop with
      | numeric descriptor => exact Numeric.numeric_progress s ambient f rest after descriptor typed
      | nop => simp [astep, advance]
      | unreachable => simp [astep]
      | drop => exact drop_progress s ambient f rest after typed
      | const ty value => exact const_progress s ambient f rest after ty value typed
      | add ty => exact add_progress s ambient f rest after ty typed
      | sub ty => exact sub_progress s ambient f rest after ty typed
      | eqz ty => exact eqz_progress s ambient f rest after ty typed
      | eq ty => exact relation_progress s ambient f rest after ty .EQ (Or.inl rfl) typed
      | lt_u ty => exact relation_progress s ambient f rest after ty (.LT .U) (Or.inr rfl) typed
      | local_get index => cases index with | mk_uN i => exact local_get_progress s ambient f rest after i typed
      | local_set index => cases index with | mk_uN i => exact local_set_progress s ambient f rest after i typed
      | local_tee index => cases index with | mk_uN i => exact local_tee_progress s ambient f rest after i typed
      | block bt body _ => exact block_progress s ambient f rest after bt body typed
      | loop bt body _ => exact loop_progress s ambient f rest after bt body typed
      | ifelse bt yes no _ _ => exact if_progress s ambient f rest after bt yes no typed
      | br depth => cases depth with | mk_uN i => exact br_progress s ambient f rest after i typed
      | br_if depth => cases depth with | mk_uN i => exact br_if_progress s ambient f rest after i typed
      | call index => cases index with | mk_uN i => exact call_progress s ambient f rest after i functions typed
      | ret => exact return_progress s ambient f rest after typed

/-- Progress for the integer slice is derived from generated source typing,
without a no-stuck assumption in the state invariant. -/
theorem astep_progress (s : AState) (typed : ATyped s) (slice : SliceState s) :
    astep s ≠ .stuck := by
  rcases s with ⟨store, ambient, frames, results⟩
  cases frames with
  | nil => simp [astep]
  | cons f rest =>
    have hresults := typed.activeResults (by simp)
    change results = [] at hresults
    subst results
    cases typed.frames with
    | cons hf hr =>
      exact frame_progress store ambient f rest typed.functions hf
        (slice.active f (by simp)).1

end Exec.Abs
