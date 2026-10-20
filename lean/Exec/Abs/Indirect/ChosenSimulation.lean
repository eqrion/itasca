import Exec.Spec.IndirectCallSource
import Exec.Abs.Sim.ChosenCall
namespace Exec.Abs.Indirect
open SpecExt Exec.Spec
theorem chosen_indirect_call_simulation {choices : SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=firstVectorChoice) (occurrence : Nat) (s : store) (ambient : frame) (f : AFrame)
    (rest : List AFrame) (after : List instr) (table type position address : Nat) (typeIndex : idx)
    (moduleInst : moduleinst) (params results types : List valtype) (body : List instr)
    (baseValues args defaults : List val)
    (hs : wf_store s) (ha : wf_frame ambient) (hf : wf_frame f.toFrame)
    (hl : LabelsWf f.labels) (hv : Forall wf_val baseValues)
    (hc : Forall wf_instr after) (hr : Forall FrameWf rest)
    (heights : ∀ label ∈ f.labels, label.height ≤ baseValues.length)
    (resolve : IndirectTarget s f.toFrame table type position address)
    (tableBound : table<2^32) (typeBound : type<2^32) (positionBound : position<2^32)
    (lookup : s.FUNCS[address]? = some ⟨⟨.mk_list params, .mk_list results⟩, moduleInst,
      .FUNC typeIndex (types.map local.LOCAL) body⟩)
    (nonbot : Forall (fun ty => ty ≠ valtype.BOT) types)
    (hdefaults : defaultLocals (types.map local.LOCAL) = some defaults)
    (hargs : Forall wf_val args) (hlen : args.length = params.length) :
    ChosenStepsN choices occurrence 2
      (decode ⟨s, ambient, { f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after, vals := baseValues ++ args ++ [integerVal .I32 position] } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have first := stepH_neutral_chosen admissible vector occurrence
    (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
    (by simp only [trapCode,Segment.i32,neutralActive])
  have second := stepH_neutral_chosen admissible vector (occurrence+1)
    (call_invoke s f.toFrame address typeIndex moduleInst params results types body args defaults hs hf lookup nonbot hdefaults hargs hlen)
    (by simp only [trapCode,neutralActive_vals,neutralActive])
  have h₁ := choice_step_instrs admissible first args (after.map admininstr_instr) hargs (wf_instrs hc)
  have h₂ := choice_step_instrs admissible second [] (after.map admininstr_instr) (forall_nil _) (wf_instrs hc)
  have h₃ := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible h₁ f.labels baseValues hl hv) ha hr
  have h₄ := choice_active admissible ambient rest f.arity
    (choice_decodeLabels admissible h₂ f.labels baseValues hl hv) ha hr
  simp only [vals, List.map_nil, List.nil_append, List.append_assoc] at h₃ h₄
  have both := ChosenStepsN.cons h₃ (ChosenStepsN.cons h₄ (ChosenStepsN.refl (occurrence+1+1) (h₄.wf admissible).2))
  simp only [decode, decodeFrames, vals, List.map_nil, List.nil_append, List.map_cons,
    AFrame.toFrame, AFrame.arity, decodeLabels, Label.arity, List.take_zero,
    List.drop_zero, List.append_nil]
  rw [List.append_assoc]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr, integerVal, Segment.i32, numtype_Inn, admininstr_val] using both

end Exec.Abs.Indirect
