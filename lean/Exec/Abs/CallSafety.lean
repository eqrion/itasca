import Exec.Abs.ControlSafety

namespace Exec.Abs
open SpecExt Exec.Spec Itasca.DeclarativeComplete

theorem zero_float_wf (ty : Fnn) :
    wf_val (.CONST (numtype_Fnn ty) (.mk_num__1 ty (.POS (.SUBNORM 0)))) := by
  apply wf_val.val_case_0
  apply wf_num_.num__case_1 _ _ _ ?_ rfl
  apply wf_fN.fN_case_0
  exact wf_fNmag.fNmag_case_1 _ _ _ ⟨by positivity, rfl⟩

/-- Zero/null local defaults inhabit their exact declared Wasm value type. -/
theorem defaultValue_typed {s : store} (hs : wf_store s) (ty : valtype)
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

theorem defaultLocals_typed {s : store} (hs : wf_store s) (types : List valtype)
    (h : Forall (fun ty => ty ≠ valtype.BOT) types) :
    ∃ values, defaultLocals (types.map local.LOCAL) = some values ∧ ResultsTyped s types values := by
  induction types with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons ty types ih =>
    obtain ⟨value, hv, hvt⟩ := defaultValue_typed hs ty (h ty (by simp))
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
    obtain ⟨defaults, hd, hdt⟩ := defaultLocals_typed hs types nonbot
    refine ⟨defaults, hd, ?_⟩
    let C' : context := { C with LOCALS := params ++ types, LABELS := [], RETURN := some (.mk_list results) }
    have hv : ResultsTyped s (params ++ types) (args ++ defaults) := List.rel_append ha hdt
    have hmap := results_type_of_typed hv
    have hw : wf_context (labelContext C' []) := wf_context_scope bindings.wf _ _ _
    apply FrameTyped.mk (f := ⟨address, results, args ++ defaults, m, [⟨results, results, [], 0, []⟩], body, []⟩) C' (bindings.scope _ _ _) hmap.symm hv (.nil) rfl ?_
      (.frame_case_ _ _ (resultsTyped_wf hv) hm)
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
        codeStack_after_bounds (value_types_concrete f.vals) hc
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
          apply resultsTyped_drop (before := front)
          simpa only [hstack] using values
        have hargtypes := results_type_of_typed hargs
        have hfront : (f.vals.take front.length).map valueType = front := by
          rw [List.map_take, hstack, List.take_left]
        have hcaller : FrameTyped s { f with vals := f.vals.take front.length, code := after } outs := by
          apply FrameTyped.mk (f := { f with vals := f.vals.take front.length, code := after }) C
            bindings localTypes locals (resultsTyped_take front.length values) returns ?_ hw
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
          · exact frameTyped_heights hcallee
          · exact hcallerHeights
          · exact typed.heights frame (by simp [hm])

end Exec.Abs
