import Itasca.Runtime.Abs.CallSafety
import Itasca.Runtime.Abs.Sim.Return

namespace Itasca.Runtime.Abs
open SpecExt Itasca.Runtime.Spec

theorem defaultValue_relation (ty : valtype) (h : ty ≠ .BOT) :
    fun_default_ ty (defaultValue ty) := by
  cases ty with
  | I32 => exact .fun_default__case_0 (integer_val_wf .I32 0 (by decide))
  | I64 => exact .fun_default__case_1 (integer_val_wf .I64 0 (by decide))
  | F32 =>
    exact .fun_default__case_2 _ (.fun_fzero_case_0 _
      (.fN_case_0 _ _ (.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩))) (zero_float_wf .F32)
  | F64 =>
    exact .fun_default__case_3 _ (.fun_fzero_case_0 _
      (.fN_case_0 _ _ (.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩))) (zero_float_wf .F64)
  | V128 => exact .fun_default__case_4 (.val_case_1 _ _ (by decide) (.uN_case_0 _ _ ⟨by omega, by omega⟩))
  | FUNCREF => exact .fun_default__case_5 (.val_case_2 _)
  | EXTERNREF => exact .fun_default__case_6 (.val_case_2 _)
  | BOT => contradiction

theorem defaultLocals_relation {s : store} (hs : wf_store s) (types : List valtype)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types) (values : List val)
    (h : defaultLocals (types.map local.LOCAL) = some values) :
    List.Forall₂ (fun value ty => fun_default_ ty (some value)) values types := by
  induction types generalizing values with
  | nil => simp only [List.map_nil, defaultLocals, Option.some.injEq] at h; subst values; exact .nil
  | cons ty types ih =>
    obtain ⟨value, hv, _⟩ := defaultValue_typed hs ty (nonbot ty (by simp))
    have relation := defaultValue_relation ty (nonbot ty (by simp))
    rw [hv] at relation
    cases rest : defaultLocals (types.map local.LOCAL) with
    | none => simp [defaultLocals, hv, rest] at h
    | some tail =>
      simp [defaultLocals, hv, rest] at h
      subst values
      exact .cons relation (ih (fun ty ht => nonbot ty (by simp [ht])) tail rest)

theorem defaults_forall₂ {values : List val} {types : List valtype}
    (h : List.Forall₂ (fun value ty => fun_default_ ty (some value)) values types) :
    Forall₂ (fun value ty => fun_default_ ty value) (values.map some) types := by
  induction h with
  | nil => simp [Forall₂]
  | @cons value ty values types relation rest ih =>
    intro pair hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact relation
    · exact ih pair hp

/-- The first call reduction resolves the active module's actual function map. -/
theorem call_resolve (s : store) (f : frame) (index address : Nat)
    (hs : wf_store s) (hf : wf_frame f)
    (lookup : f.MODULE.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32) :
    StepH ⟨⟨s, f⟩, [.CALL (.mk_uN index)]⟩ [] ⟨⟨s, f⟩, [.CALL_ADDR address]⟩ := by
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp lookup
  have hsource : wf_config ⟨⟨s, f⟩, [.CALL (.mk_uN index)]⟩ :=
    wf_config_make hs hf (by
      intro i hm; simp only [List.mem_singleton] at hm; subst i
      exact .admininstr_case_10 _ (integer_uN_wf .I32 index hi32))
  have htarget : wf_config ⟨⟨s, f⟩, [.CALL_ADDR address]⟩ :=
    wf_config_make hs hf (by intro i hm; simp only [List.mem_singleton] at hm; subst i; exact .admininstr_case_70 _)
  apply StepH.step
  apply Step.read _ _ _ ?_ hsource htarget
  simpa only [fun_funcaddr, proj_uN_0, getElem!_pos f.MODULE.FUNCS index hi, heq] using
    Step_read.call ⟨s, f⟩ (.mk_uN index) hi hsource (.admininstr_case_70 _)

theorem store_function_wf {s : store} (hs : wf_store s) {fn : funcinst}
    (hm : fn ∈ s.FUNCS) : wf_funcinst fn := by
  cases hs with | store_case_ _ _ _ _ _ _ funcs _ _ _ _ => exact funcs fn hm

/-- The address call rule creates exactly the callee frame and result label,
using the concrete declared local defaults. -/
theorem call_invoke (s : store) (f : frame) (address : Nat) (index : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (args defaults : List val) (hs : wf_store s) (hf : wf_frame f)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC index (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepH ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR address]⟩ []
      ⟨⟨s, f⟩, [.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
        [.LABEL_ results.length [] (body.map admininstr_instr)]]⟩ := by
  obtain ⟨hi, hlookup⟩ := List.getElem?_eq_some_iff.mp lookup
  have hfn := store_function_wf hs (List.mem_of_getElem? lookup)
  have hm := function_module_wf hs (List.mem_of_getElem? lookup)
  have hfunc : wf_func (.FUNC index (types.map local.LOCAL) body) := by
    cases hfn with
    | funcinst_case_ _ _ _ _ hc =>
      cases hc with | funccode_case_0 _ _ _ hi hb => exact .func_case_0 _ _ _ hi hb
  have hbody : Forall wf_instr body := by cases hfunc; assumption
  obtain ⟨values, hv, hvalues⟩ := defaultLocals_typed hs types nonbot
  have heq : values = defaults := Option.some.inj (hv.symm.trans hdefaults)
  subst values
  have hdlen := resultsTyped_length hvalues
  have hlocals := forall_append hargs (resultsTyped_wf hvalues)
  have hframe : wf_frame ⟨args ++ defaults, moduleInst⟩ := .frame_case_ _ _ hlocals hm
  have hlabel : wf_admininstr (.LABEL_ results.length [] (body.map admininstr_instr)) :=
    .admininstr_case_71 _ _ _ (forall_nil _) (wf_instrs hbody)
  have hwrap : wf_admininstr (.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
      [.LABEL_ results.length [] (body.map admininstr_instr)]) :=
    .admininstr_case_72 _ _ _ hframe (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hlabel)
  have hsource : wf_config ⟨⟨s, f⟩, vals args ++ [.CALL_ADDR address]⟩ :=
    wf_config_make hs hf (forall_append (wf_vals hargs)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact .admininstr_case_70 _))
  have htarget : wf_config ⟨⟨s, f⟩, [.FRAME_ results.length ⟨args ++ defaults, moduleInst⟩
      [.LABEL_ results.length [] (body.map admininstr_instr)]]⟩ :=
    wf_config_make hs hf (by intro i hi; simp only [List.mem_singleton] at hi; subst i; exact hwrap)
  apply StepH.step
  apply Step.read _ _ _ ?_ hsource htarget
  apply Step_read.call_addr ⟨s, f⟩ args.length args address results.length
    ⟨args ++ defaults, moduleInst⟩ body params results moduleInst
    (.FUNC index (types.map local.LOCAL) body) index types (defaults.map some)
  · simpa only [List.length_map] using hdlen
  · exact defaults_forall₂ (defaultLocals_relation hs types nonbot defaults hdefaults)
  · exact hi
  · simpa only [fun_funcinst, funccode_func, getElem!_pos s.FUNCS address hi] using hlookup
  · rfl
  · intro value hv
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
    simp
  · simp [Map, List.map_map, Function.comp_def, Option.get!]
  · exact hsource
  · exact hwrap
  · exact hfn
  · exact hfunc
  · simpa [Map, List.map_map, Function.comp_def, Option.get!] using hframe
  · rfl
  · exact hlen
  · rfl

/-- A defined direct call resolves its address, then installs the actual callee
frame. The caller's operands and all suspended contexts are preserved. -/
theorem call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index address : Nat) (typeIndex : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (baseValues args defaults : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : f.module.FUNCS[index]? = some address) (hi32 : index < 2 ^ 32)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    StepsHN 2
      (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have h₁ := stepH_instrs (call_resolve s f.toFrame index address hs hf resolve hi32)
    args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := stepH_instrs (call_invoke s f.toFrame address typeIndex moduleInst
    params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := stepH_active ambient rest f.arity
    (stepH_decodeLabels h₁ f.labels baseValues hl hv) ha hr
  have h₄ := stepH_active ambient rest f.arity
    (stepH_decodeLabels h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := StepsHN.cons h₃ (StepsHN.cons h₄ (StepsHN.refl (stepH_wf h₄).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using both

theorem function_local_types {C : context} {index : idx} {locals : List «local»}
    {body : List instr} {ft : functype} (h : Func_ok C (.FUNC index locals body) ft) :
    ∃ types, locals = types.map local.LOCAL ∧ Forall (fun ty => ty ≠ valtype.BOT) types := by
  cases h
  exact ⟨_, rfl, by assumption⟩

/-- No operational call premise is postulated: address resolution, signature,
local defaults, and stack arguments follow from the source typing invariant. -/
theorem typed_call_simulation (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩ = .next next) :
    StepsHN 2 (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩) [] (decode next) := by
  have frames := typed.frames
  cases frames with
  | cons hf hr =>
    cases hf with
    | mk C bindings localTypes locals values returns hc hw =>
      simp only [List.append_nil] at hc
      obtain ⟨front, ins, outs, hop, hstack, hafter, heights⟩ :=
        codeStack_after_bounds (value_types_concrete f.vals) hc
      cases hop with
      | call _ _ inputs outputs hi ht hC hinst =>
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
          apply resultsTyped_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hi32 : index < 2 ^ 32 := by
          cases hinst with
          | instr_case_10 _ hu => cases hu with
            | uN_case_0 _ bounds => norm_num at bounds ⊢; omega
        cases hcode : fn.CODE with
        | HOST host =>
          simp [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode] at step
        | FUNC fi fl body =>
          have htyped := typed.functions fn (List.mem_of_getElem? hfn)
          simp only [hcode] at htyped
          obtain ⟨Cfn, hbindings, hlocals, hlabels, _, hfunc⟩ := htyped
          rw [htype'] at hfunc
          obtain ⟨types, hfl, nonbot⟩ := function_local_types hfunc
          subst fl
          obtain ⟨defaults, hdefaults, hdefaultTypes⟩ := defaultLocals_typed typed.store types nonbot
          have hrecord : fn = ⟨⟨.mk_list ins, .mk_list outs⟩, fn.MODULE,
              .FUNC fi (types.map local.LOCAL) body⟩ := by
            cases fn
            simp_all
          have result := call_simulation s ambient f rest after index (f.module.FUNCS[index]) fi
            fn.MODULE ins outs types body (f.vals.take front.length) (f.vals.drop front.length) defaults
            typed.store typed.ambient hw (codeStack_labels_wf hc)
            (fun v hv => resultsTyped_wf values v (List.mem_of_mem_take hv))
            (fun i hm => codeStack_wf hc i (by simp [hm])) (framesTyped_wf hr)
            (by intro label hm; have hh := heights label hm; simp only [List.length_take]; omega)
            hresolve hi32 (hrecord ▸ hfn) nonbot hdefaults (resultsTyped_wf hargs) (resultsTyped_length hargs)
          have hnext : next = ⟨s, ambient,
              ⟨f.module.FUNCS[index], outs, f.vals.drop front.length ++ defaults, fn.MODULE,
                [⟨outs, outs, [], 0, []⟩], body, []⟩ ::
              { f with vals := f.vals.take front.length, code := after } :: rest, []⟩ := by
            simpa [astep, call, hresolve, hfn, htype', hbound, hheight, hargtypes, hcode, hdefaults] using step.symm
          rw [hnext]
          simpa only [List.take_append_drop] using result

end Itasca.Runtime.Abs
