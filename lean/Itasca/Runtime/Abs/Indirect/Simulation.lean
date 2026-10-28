import Itasca.Runtime.Spec.IndirectCallSource
import Itasca.Runtime.Abs.Sim.Call
namespace Itasca.Runtime.Abs.Indirect
open SpecExt Itasca.Runtime.Spec
theorem indirect_call_simulation (s : store) (ambient : frame) (f : AFrame)
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
    StepsHN 2
      (decode ⟨s, ambient, { f with code := .CALL_INDIRECT (.mk_uN table) (.mk_uN type) :: after, vals := baseValues ++ args ++ [integerVal .I32 position] } :: rest, []⟩) []
      (decode ⟨s, ambient,
        ⟨address, results, args ++ defaults, moduleInst,
          [⟨results, results, [], 0, []⟩], body, []⟩ ::
        { f with code := after, vals := baseValues } :: rest, []⟩) := by
  have h₁ := stepH_instrs (call_indirect_resolve s f.toFrame table type position address hs hf tableBound typeBound positionBound resolve)
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
  rw [List.append_assoc]
  rw [decodeLabels_move_values _ _ _ _ heights]
  simpa [instrContext, vals, List.append_assoc, AFrame.arity, AFrame.toFrame, admininstr_instr, integerVal, Segment.i32, numtype_Inn, admininstr_val] using both

end Itasca.Runtime.Abs.Indirect
