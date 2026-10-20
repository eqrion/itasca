import Exec.Abs.Sim.Call
import Exec.Abs.Sim.NeutralDecode
import Exec.Abs.Sim.ChosenContext
namespace Exec.Abs
open SpecExt Exec.Spec

theorem chosen_call_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
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
    ChosenStepsN choices occurrence 2
      (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after, vals := baseValues ++ args } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have first := stepH_neutral_chosen admissible vector occurrence
    (call_resolve s f.toFrame index address hs hf resolve hi32) (by simp only [trapCode,neutralActive])
  have second := stepH_neutral_chosen admissible vector (occurrence+1)
    (call_invoke s f.toFrame address typeIndex moduleInst params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    (by simp only [trapCode,neutralActive_vals,neutralActive])
  have h₁ := choice_step_instrs admissible first
    args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := choice_step_instrs admissible second
    [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible h₁ f.labels baseValues hl hv) ha hr
  have h₄ := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := ChosenStepsN.cons h₃ (ChosenStepsN.cons h₄ (ChosenStepsN.refl (occurrence+1+1) (h₄.wf admissible).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr] using both

theorem chosen_typed_call_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (index : Nat) (next : AState)
    (typed : ATyped ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩)
    (step : astep ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩ = .next next) :
    ChosenStepsN choices occurrence 2 (decode ⟨s, ambient, { f with code := .CALL (.mk_uN index) :: after } :: rest, []⟩) [] (decode next) := by
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
          have result := chosen_call_simulation admissible vector occurrence s ambient f rest after index (f.module.FUNCS[index]) fi
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

end Exec.Abs
