import Itasca.Body.ControlComplete
import Itasca.Body.CompletenessFrame

open Aeneas Aeneas.Std

namespace Itasca.Completeness

theorem Frame.output_unreachable {st} (f : Frame st) {s : code.OpIterState}
    (hc : s.ctrls.val = f.parents ++ [{ f.current with polymorphic_base := true }])
    (hv : s.vals.val = f.outer) (out : List valtype) : f.Output out s :=
  ⟨true, [], hc, by simpa using hv, Sequence.realizes_polymorphic_empty out⟩

theorem step_br {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (C : context)
    (idx : U32) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hbytes : Wasm.BytesAt data st.pos bytes next) (he : Leb128.Encoding bytes idx.val)
    (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hprim : Instr_ok C (.BR (.mk_uN idx.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input)) :
    StepResult f data env ctx code.OP_BR next (front ++ output) := by
  cases hprim with
  | br C label before target out hd hlookup hC hw =>
    simp only [proj_uN_0] at hlookup
    have hdepth : idx.val < st.ctrls.val.length := by simpa [hlabels, Control.labels, proj_uN_0] using hd
    let targetCtrl := st.ctrls.val[st.ctrls.val.length - 1 - idx.val]'(by omega)
    have htypes : target = (Control.targetTypes targetCtrl).map Translate.valueType := by
      rw [hlabels, getElem!_pos _ _ (by simpa [Control.labels] using hdepth),
        Control.labels_lookup st.ctrls.val idx.val hdepth] at hlookup
      simpa [targetCtrl, proj_list_0] using hlookup.symm
    obtain ⟨⟨_, s⟩, hr, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
      (code.read_br.complete st data idx next targetCtrl f.parents f.current f.outer f.operands
        (front ++ before) (hbytes.u32_decoded idx he) hdepth rfl f.ctrls f.vals f.base
        (by simpa [htypes, List.append_assoc] using ht))
    dsimp only at hv hc hp
    refine ⟨s, ?_, hp, f.output_unreachable hc hv _, ?_⟩
    · exact code.step_br _ st s data env ctx idx targetCtrl.block_type () () hr rfl
    · simp only [hv, f.vals, List.length_append]
      omega

theorem step_br_if {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (C : context)
    (idx : U32) (bytes : List U8) (next : Usize) (front input output : List valtype)
    (hbytes : Wasm.BytesAt data st.pos bytes next) (he : Leb128.Encoding bytes idx.val)
    (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hsize : st.vals.val.length < Usize.max)
    (hprim : Instr_ok C (.BR_IF (.mk_uN idx.val)) (.mk_functype (.mk_list input) (.mk_list output)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input)) :
    StepResult f data env ctx code.OP_BR_IF next (front ++ output) := by
  cases hprim with
  | br_if C label target hd hlookup hC hw =>
    simp only [proj_uN_0] at hlookup
    have hdepth : idx.val < st.ctrls.val.length := by simpa [hlabels, Control.labels, proj_uN_0] using hd
    let targetCtrl := st.ctrls.val[st.ctrls.val.length - 1 - idx.val]'(by omega)
    have htypes : output = (Control.targetTypes targetCtrl).map Translate.valueType := by
      rw [hlabels, getElem!_pos _ _ (by simpa [Control.labels] using hdepth),
        Control.labels_lookup st.ctrls.val idx.val hdepth] at hlookup
      simpa [targetCtrl, proj_list_0] using hlookup.symm
    obtain ⟨⟨_, s⟩, hr, rfl, hc, hp, rest, hv, hl, ht'⟩ := WP.spec_imp_exists
      (code.read_br_if.complete st data idx next targetCtrl f.outer f.operands front
        (hbytes.u32_decoded idx he) hdepth rfl f.vals f.base_eq hsize
        (by simpa [f.poly_eq, htypes, List.append_assoc] using ht))
    dsimp only at hc hp hv hl ht'
    refine ⟨s, ?_, hp, f.output_of_same_ctrls hc hv (by simpa [htypes] using ht'), ?_⟩
    · simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        code.OpVisitor.on_br_if.default]
    · simp only [hv, f.vals, List.length_append]
      omega

theorem step_return {st : code.OpIterState} (f : Frame st) (data : Slice U8)
    (env : module.Env) (ctx : code.Context) (C : context)
    (next : Usize) (front input output : List valtype)
    (hbytes : Wasm.BytesAt data st.pos [] next)
    (hreturn : C.RETURN = some (.mk_list (ctx.results.val.map Translate.valueType)))
    (hprim : Instr_ok C .RETURN (.mk_functype (.mk_list input) (.mk_list output)))
    (ht : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ input)) :
    StepResult f data env ctx code.OP_RETURN next (front ++ output) := by
  cases hprim with
  | «return» C before target out hret hC hw =>
    have htypes : target = ctx.results.val.map Translate.valueType := by
      simpa using hret.symm.trans hreturn
    obtain ⟨⟨_, s⟩, hr, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
      (code.read_return.complete st ctx f.parents f.current f.outer f.operands (front ++ before)
        f.ctrls f.vals f.base (by simpa [htypes, List.append_assoc] using ht))
    dsimp only at hv hc hp
    refine ⟨s, ?_, hp.trans hbytes.empty.symm, f.output_unreachable hc hv _, ?_⟩
    · simp [global_simps, hr, code.visit, core.result.Result.Insts.CoreOpsTry.branch,
        code.OpVisitor.on_return.default]
    · simp only [hv, f.vals, List.length_append]
      omega

end Itasca.Completeness
