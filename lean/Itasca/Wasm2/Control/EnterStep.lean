import Itasca.Wasm2.Control.EnterComplete
import Itasca.Wasm2.Totality

/-!
# `block`, `loop` and `if` step

`Pending.enter_after` shows that `code.enter` for `block` (`0x02`), `loop` (`0x03`) and `if`
(`0x04`) preserves `Pending`, by pushing a fresh frame onto the typed zipper with
`Frames.Open.enter_child`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The syntax token that opens a frame of the given initial form. -/
def Frames.Form.token (form : Frames.Form) (bt : signature.BlockType) : Token :=
  match form with
  | .loop => .loop bt
  | .then_ => .if_ bt
  | _ => .block bt

/-- The opcode byte that opens a frame of the given initial form. -/
def Frames.Form.opcode (form : Frames.Form) : U8 :=
  match form with
  | .loop => 0x03#u8
  | .then_ => 0x04#u8
  | _ => 0x02#u8

/-- Opening a `block`, `loop` or `if` frame with `code.enter` preserves `Pending` on success. -/
theorem Pending.enter_after {data env profile locals index st} (p : Pending data env profile locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (hbyte : data.val[p.start.val]'p.inbounds = form.opcode) :
    code.enter st data env profile form.kind ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hcap : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply WP.spec_mono (code.enter.sound st data env profile form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.opened.shape.core hcap)
  intro r hr hok
  obtain ⟨bt, ins, outs, hdecoded, hscalar, hin, hout, hip, hop, remaining, newBase,
    hlen, hbase, hpop, hctrls, hblocks, hvals⟩ := hr hok
  have encoded : At data p.start (form.token bt) r.2.core.pos := by
    apply At.of_block_type bt p.inbounds hbyte p.pos _ hdecoded
    intro bytes hbytes
    rcases initial with rfl | rfl | rfl
    · exact .block hbytes
    · exact .loop hbytes
    · exact .if_ hbytes
  obtain ⟨ho, htrace⟩ := p.opened.enter_child
    (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩) form bt ins outs initial hin hout
    newBase remaining (by simpa [Control.polymorphic, ctrls] using hpop)
    (by simpa [base] using hbase) hctrls hblocks
    (by simpa [vals, base] using hvals)
  refine p.running_after r.2 _ _ (form.token bt) encoded ho ?_ ?_ ?_
    (p.profileFrames.enter form initial bt ins outs newBase remaining hscalar) ?_
    (by cases form <;> simp [Frames.Form.token, Token.Declared])
  · simpa [Frames.bodyType_enter] using p.bodyType
  · have he : form.opening bt = [form.token bt] := by
      rcases initial with rfl | rfl | rfl <;> rfl
    simpa [he] using htrace
  · simp [hblocks]
  · intro hp
    refine p.wasm1_at encoded ?_ ?_ hp
    · rw [hbyte]; rcases initial with rfl | rfl | rfl <;> decide
    · rcases initial with rfl | rfl | rfl <;> exact hscalar hp

end Itasca.Wasm2
