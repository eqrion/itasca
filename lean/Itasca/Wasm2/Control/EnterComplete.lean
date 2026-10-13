import Itasca.Wasm2.Control.EnterSound

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

theorem checkBlock.complete (env : module.Env) (bt : signature.BlockType)
    (ins outs : List types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000) :
    checkBlock env bt = .ok (.Ok ()) := by
  cases bt with
  | Empty | Value _ => rfl
  | TypeIndex index =>
    have hi : index.val < env.types.val.length := by
      by_contra hn
      simp [inputs, resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at hin
    have hins : env.types.val[index.val].params.val = ins := by
      simpa [inputs, resolve, List.getElem?_eq_getElem hi] using hin
    have houts : env.types.val[index.val].results.val = outs := by
      simpa [outputs, resolve, List.getElem?_eq_getElem hi] using hout
    have hspec : checkBlock env (.TypeIndex index) ⦃ r => r = .Ok () ⦄ := by
      unfold checkBlock
      step
      split
      · scalar_tac
      · step as ⟨ft, hft⟩
        have hf : ft = env.types.val[index.val] := by simpa [r_post] using hft
        rw [code.check_func_type.complete ft (by simpa [hf, hins] using hip)
          (by simpa [hf, houts] using hop)]
        simp
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hspec
    exact hr

/-- Forward realization and exact effects after opening, used by recursive
independent completeness rather than assuming an accepted handler. -/
def EnterForward (st s : code.BodyState) (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List types.ValueType) (outer segment : List code.StackType) (ts : List valtype) : Prop :=
  ∃ remaining base,
    remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
    Sequence.Realizes (Control.polymorphic st.core) remaining ts ∧
    s.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    s.blocks.val = st.blocks.val ++ [bt] ∧
    s.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val

theorem enterParams.complete (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ ins.map Translate.valueType)) :
    enterParams st env form.kind bt ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = st.core.pos ∧
      EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  unfold enterParams
  simp only [signature.BlockType.params.spec, bind_ok]
  step with code.pop_results.complete st.core env (inputs bt) ins outer segment ts hin hv hb ht
    as ⟨r, s, hr, hc, hp, remaining, hv', hl, ht'⟩
  simp only [hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with code.push_frame.spec { st with core := s } form.kind bt (by simpa [hc] using hcap)
    as ⟨s1, hc1, hv1, hp1, hb1⟩
  step with code.push_results.spec s1.core env (inputs bt) ins hin (by
    simp only [hv1, hv', hv, List.length_append] at *; omega)
    as ⟨r1, s2, hok, hvs, hc2, hp2⟩
  refine ⟨hok, hp2.trans (hp1.trans hp), remaining, alloc.vec.Vec.len s.vals, hl,
    by simp [hv'], ht', ?_, by simpa [hc2, hc] using hb1, ?_⟩
  · simp [hc2, hc1, hc, Frames.Saved.fresh, Wasm2.frame]
  · simpa [hv1, hv'] using hvs

theorem enterArgs.complete (st : code.BodyState) (env : module.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype) (initial : form.Initial)
    (hin : resolve env (inputs bt) = some ins)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ form.args ins)) :
    enterArgs st env form.kind bt ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = st.core.pos ∧
      EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  rcases initial with rfl | rfl | rfl
  · simpa [enterArgs, Frames.Form.kind, Frames.Form.args] using
      enterParams.complete st env .block bt ins outs outer segment ts hin hv hb hcap hvalsCap (by simpa [Frames.Form.args] using ht)
  · simpa [enterArgs, Frames.Form.kind, Frames.Form.args] using
      enterParams.complete st env .loop bt ins outs outer segment ts hin hv hb hcap hvalsCap (by simpa [Frames.Form.args] using ht)
  · obtain ⟨v, s, rest, hr, hc, hp, hv', hl, hvtype, ht'⟩ :=
      code.pop_with_type.complete st.core outer segment (ts ++ ins.map Translate.valueType) .I32 hv hb
        (by simpa [Frames.Form.args, List.append_assoc, Translate.valueType] using ht)
    have heq : enterArgs st env .Then bt = enterParams { st with core := s } env .Then bt := by
      simp [enterArgs, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [show Frames.Form.then_.kind = code.LabelKind.Then from rfl, heq]
    apply WP.spec_mono (enterParams.complete { st with core := s } env .then_ bt ins outs outer rest ts
      hin hv' (by simpa [Control.base, hc] using hb) (by simpa [hc] using hcap)
      (by simp only [hv, hv', List.length_append] at *; omega)
      (by simpa [Control.polymorphic, hc] using ht'))
    intro result hresult
    obtain ⟨hok, hpos, remaining, base, hlen, hbase, htyped, hctrl, hblocks, hvals⟩ := hresult
    exact ⟨hok, hpos.trans hp, remaining, base, hlen.trans hl, hbase,
      by simpa [Control.polymorphic, hc] using htyped, by simpa [hc] using hctrl, by simpa [hc] using hblocks, hvals⟩

end Itasca.Wasm2

namespace Itasca

/-- Every compatible independently encoded structured entry is accepted,
including indexed parameters/results and the if condition. -/
theorem code.enter.complete (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (form : Wasm2.Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (next : Usize) (ins outs : List types.ValueType)
    (outer segment : List code.StackType) (ts : List valtype)
    (hdecoded : Wasm2.BlockDecoded data st.core.pos bt next)
    (hin : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (hout : Wasm2.resolve env (Wasm2.outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000)
    (hv : st.core.vals.val = outer ++ segment) (hb : (Control.base st.core).val = outer.length)
    (hcap : st.blocks.val.length < Usize.max)
    (hvalsCap : st.core.vals.val.length + ins.length ≤ Usize.max)
    (ht : Sequence.Realizes (Control.polymorphic st.core) segment (ts ++ form.args ins)) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () ∧ r.2.core.pos = next ∧
      Wasm2.EnterForward st r.2 form bt ins outs outer segment ts ⦄ := by
  rw [Wasm2.enter_eq, signature.read_block_type.complete data st.core.pos bt next hdecoded]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [Wasm2.checkBlock.complete env bt ins outs hin hout hip hop]
  simp only [bind_ok]
  exact Wasm2.enterArgs.complete { st with core := { st.core with pos := next } } env form bt
    ins outs outer segment ts initial hin hv hb hcap hvalsCap ht

end Itasca
