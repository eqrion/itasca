import Itasca.Wasm1.Complete.Frame
import Itasca.Handler.BrTableComplete

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Completeness

private theorem resultTypes_injective : Function.Injective Control.resultTypes := by
  intro a b h
  cases a with
  | Empty => cases b <;> simp_all [Control.resultTypes, Control.results]
  | Value a =>
      cases b with
      | Empty => simp [Control.resultTypes, Control.results] at h
      | Value b =>
          have he : Translate.valueType a = Translate.valueType b := by
            simpa [Control.resultTypes, Control.results] using h
          exact congrArg code.BlockType.Value (Translate.valueType_injective he)

/-- Wasm 1.0 target homogeneity strengthens the generated branch-table rule
    enough to force the actual handler and dispatcher to accept. -/
theorem Frame.step_brTable {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (depths : List U32) (default : U32)
    (count entries final : List U8) (next : Usize)
    (C : context) (front ins outs : List valtype)
    (hcount : Leb128.Encoding count depths.length) (hentries : Wasm1.IndicesEncoding depths entries)
    (hdefault : Leb128.Encoding final default.val)
    (hbytes : Wasm1.BytesAt data st.pos (count ++ entries ++ final) next)
    (hlabels : C.LABELS = Control.labels st.ctrls.val)
    (hprofile : Wasm1.SameTargets C (depths.map (fun d => .mk_uN d.val)) (.mk_uN default.val))
    (ht : Instr_ok C (BrTable.instruction depths default)
      (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.current.polymorphic_base f.operands (front ++ ins)) :
    StepResult f data env ctx 0x0E#u8 next (front ++ outs) := by
  cases ht with
  | br_table _ _ _ before args after hbounds _ hfallback hsub _ _ =>
      have hdf : default.val < st.ctrls.val.length := by
        simpa [proj_uN_0, hlabels, Control.labels] using hfallback
      let bt := Control.targetBlockType (st.ctrls.val[st.ctrls.val.length - 1 - default.val]'(by omega))
      have lookup (idx : U32) (hi : idx.val < st.ctrls.val.length) :
          C.LABELS[idx.val]! = .mk_list
            (Control.resultTypes (Control.targetBlockType
              (st.ctrls.val[st.ctrls.val.length - 1 - idx.val]'(by omega)))) := by
        rw [hlabels, getElem!_pos _ _ (by simpa [Control.labels] using hi),
          Control.labels_lookup st.ctrls.val idx.val hi]
        rfl
      have htarget : BrTable.Targets st.ctrls.val (depths ++ [default]) (some bt) := by
        intro idx hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hm | rfl
        · have hi : idx.val < st.ctrls.val.length := by
            have hh := hbounds (.mk_uN idx.val) (by simpa using List.mem_map.mpr ⟨idx, hm, rfl⟩)
            simpa [proj_uN_0, hlabels, Control.labels] using hh
          refine ⟨hi, congrArg some (resultTypes_injective ?_)⟩
          have he := hprofile (.mk_uN idx.val) (List.mem_map.mpr ⟨idx, hm, rfl⟩)
          simp only [proj_uN_0, lookup idx hi, lookup default hdf, list.mk_list.injEq] at he
          exact he.symm
        · exact ⟨hdf, rfl⟩
      have hargs : Resulttype_sub (.mk_list args) (.mk_list (Control.resultTypes bt)) := by
        simpa only [proj_uN_0, lookup default hdf] using hsub
      have hrequired : Sequence.Realizes (Control.polymorphic st) f.operands
          ((front ++ before) ++ Control.resultTypes bt ++ [.I32]) := by
        have hwide := DeclarativeComplete.realizes_mono hr
          (DeclarativeComplete.result_sub_append (DeclarativeComplete.result_sub_refl front)
            (DeclarativeComplete.result_sub_append (DeclarativeComplete.result_sub_refl before)
              (DeclarativeComplete.result_sub_append hargs (DeclarativeComplete.result_sub_refl [.I32]))))
        simpa [f.poly_eq, List.append_assoc] using hwide
      obtain ⟨s, w, hs, hc, hp, hv⟩ := code.read_br_table.complete
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        (by intros; exact ⟨(), rfl⟩) st data () f.parents f.current f.outer f.operands
        (front ++ before) bt depths default next f.ctrls f.vals f.base
        (hbytes.br_table_decoded depths default hcount hentries hdefault) htarget hrequired
      cases w
      refine ⟨s, ?_, hp, ⟨true, [], hc, by simpa using hv,
        Sequence.realizes_polymorphic_empty _⟩, ?_⟩
      · rw [show (0x0E#u8) = code.OP_BR_TABLE from by simp [global_simps],
          code.step_br_table.dispatch]
        simp [hs, CoreVisitor.run, code.OpVisitor.on_br_table.default, code.visit,
          core.result.Result.Insts.CoreOpsTry.branch]
      · simp only [hv, f.vals, List.length_append]
        omega

end Itasca.Wasm1.Completeness
