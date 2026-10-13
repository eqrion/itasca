import Itasca.Handler.ControlFlow
import Itasca.Wasm1.Frames

open Aeneas Aeneas.Std

namespace Itasca

/-- The extracted end handler either rejects or advances the complete typed syntax zipper. -/
@[step]
theorem code.read_end.wasm1_frames (root : context) (hroot : wf_context root)
    (st : code.OpIterState) (parents : List WasmFrames.Saved) (current : WasmFrames.Saved)
    (bodyBt : code.BlockType) (hopen : WasmFrames.Open root st parents current)
    (hbody : WasmFrames.bodyType parents current = some bodyBt)
    (hsize : st.vals.val.length + 1 ≤ Usize.max) :
    code.read_end st ⦃ r => r.2.pos = st.pos ∧
      ∀ result, r.1 = .Ok result →
        r.2.vals.val.length ≤ st.vals.val.length + 1 ∧
        r.2.ctrls.val.length ≤ st.ctrls.val.length ∧
        WasmFrames.Status root bodyBt r.2 (WasmFrames.trace parents current ++ [.end_]) ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, vals⟩ := id hopen
  obtain ⟨⟨result, st'⟩, hr, hp, hsem⟩ := WP.spec_imp_exists
    (code.read_end.realizes st (parents.map WasmFrames.Saved.ctrl) current.ctrl outer current.vals
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
    · have hex : ∃ op, WasmFrames.Closed current.form current.ctrl.block_type current.ops op := by
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
      rw [WasmFrames.bodyType_close, ← hparents]
      exact hbody


end Itasca
