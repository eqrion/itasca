import Itasca.Wasm1.Complete.Structured

open Aeneas Aeneas.Std

namespace Itasca.Completeness

/-- Close the body frame after executing its independently encoded and typed
instruction list, then discharge the public size and trailing-byte guards. -/
theorem body_of_programs (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (hresults : ctx.results.val = Control.results bt)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Wasm1.Emits tokens ops → Program data env ctx tokens ops)
    (hbody : Wasm1.Body data env ctx bt) :
    code.validate_body data env ctx = .ok (.Ok ()) := by
  obtain ⟨ops, hencoding, htyped, hprofile⟩ := hbody
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := Wasm1.Consumed.split hbytes
  let st := Body.initial bt
  let f : Frame st :=
    ⟨[], ⟨.Body, bt, Control.signature bt, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩
  let C := Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt
  have hmatch : EnvTranslation.Matches env ctx C :=
    (EnvTranslation.Matches.root env ctx).enter _
  have hlabels : C.LABELS = Control.labels st.ctrls.val := by
    change [list.mk_list (Control.resultTypes bt)] =
      [list.mk_list ((Control.results bt).map Translate.valueType)]
    rfl
  have hbounds := (Wasm1.State.start data env ctx bt hsize).bounds
  obtain ⟨s, hrun, hp, hout, hb⟩ := hprograms inner ops hemits C st f middle []
    (Control.resultTypes bt) hmatch hlabels hbounds hinner
      (Sequence.realizes_default false []) htyped hprofile
  obtain ⟨g, hgp, hgo, hgk, hgb, hgsig, hgba, hgr⟩ := hout.next
  have hend' : Wasm1.At data s.pos .end_ next := by simpa [hp] using hend.single
  have hthen : g.current.kind = .Then → g.current.block_type = .Empty := by
    simp [hgk, f]
  have hreal : Sequence.Realizes g.current.polymorphic_base g.operands
      (Control.resultTypes g.current.block_type) := by simpa [hgb, f] using hgr
  obtain ⟨last, hrun', hp', hc', _, _⟩ := execute_end g data env ctx next hb hend' hthen hreal
  apply (hrun.append hrun').public hresults hsize
  · simpa [hgp, f] using hc'
  · simpa [hp'] using hfinish

end Itasca.Completeness
