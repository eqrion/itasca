import Itasca.ControlFlow
import Itasca.Wasm1Frames

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted end handler either rejects or advances the complete typed syntax zipper. -/
@[step]
theorem code.read_end.wasm1_frames (root : context) (hroot : wf_context root)
    (st : code.OpIterState) (parents : List Wasm1Frames.Saved) (current : Wasm1Frames.Saved)
    (bodyBt : code.BlockType) (hopen : Wasm1Frames.Open root st parents current)
    (hbody : Wasm1Frames.bodyType parents current = some bodyBt)
    (hsize : st.vals.val.length + 1 ≤ Usize.max) :
    code.read_end st ⦃ r => r.2.pos = st.pos ∧
      ∀ result, r.1 = .Ok result →
        r.2.vals.val.length ≤ st.vals.val.length + 1 ∧
        r.2.ctrls.val.length ≤ st.ctrls.val.length ∧
        Wasm1Frames.Status root bodyBt r.2 (Wasm1Frames.trace parents current ++ [.end_]) ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id hopen
  obtain ⟨⟨result, st'⟩, hr, hp, hsem⟩ := WP.spec_imp_exists
    (code.read_end.realizes st (parents.map Wasm1Frames.Saved.ctrl) current.ctrl outer current.vals
      ctrls vals base hsize)
  dsimp only [EndResult] at hp hsem
  rw [hr, WP.spec_ok]
  refine ⟨hp, ?_⟩
  intro result' heq
  dsimp only at heq
  subst result
  obtain ⟨kind, bt⟩ := result'
  obtain ⟨rfl, rfl, hc, hv, hresults, hthen⟩ := hsem
  have hrslen : (Control.results current.ctrl.block_type).length ≤ 1 := by
    cases current.ctrl.block_type <;> simp [Control.results]
  refine ⟨?_, ?_, ?_⟩
  · simp only [hv, vals, List.length_append, List.length_map]
    omega
  · simp [hc, ctrls]
  · by_cases hform : current.form = .body
    · obtain ⟨hparents, htokens, htyped, hprofile⟩ := hopen.finish_body hform hresults
      have hbt : current.ctrl.block_type = bodyBt := by simpa [hparents] using hbody
      right
      refine ⟨by simpa [hparents] using hc, current.ops, htokens, ?_, ?_⟩
      simpa [hbt] using htyped
      simpa [hbt] using hprofile
    · have hex : ∃ op, Wasm1Frames.Closed current.form current.ctrl.block_type current.ops op := by
        cases hf : current.form with
        | body => exact False.elim (hform hf)
        | block => exact ⟨_, .block _ _⟩
        | loop => exact ⟨_, .loop _ _⟩
        | then_ =>
          have hbt := hthen (by rw [header.kind, hf]; rfl)
          rw [hbt]
          exact ⟨_, .then_ _⟩
        | else_ tokens ops => exact ⟨_, .else_ _ _ _ _⟩
      obtain ⟨op, closed⟩ := hex
      obtain ⟨gps, parent, hparents, hnext, htrace⟩ := hopen.close hroot op closed hresults hc
        (by simpa [vals, base] using hv)
      left
      refine ⟨gps, _, hnext, htrace, ?_⟩
      rw [Wasm1Frames.bodyType_close, ← hparents]
      exact hbody


end Itasca
