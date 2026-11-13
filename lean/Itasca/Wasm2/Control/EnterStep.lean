import Itasca.Wasm2.Control.EnterSound
import Itasca.Wasm2.SoundLoop

/-!
Sections, each formerly its own module: EnterComplete, EnterStep.
-/

/-! ## EnterComplete -/

section

/-!
# Completeness of block entry

Completeness of the extracted `code.enter` for `block`, `loop` and `if`. `checkBlock.complete`,
`enterParams.complete` and `enterArgs.complete` cover its pieces, `EnterForward` states the
forward effect of opening a frame, and `code.enter.complete` accepts every independently encoded
block type whose signature is compatible with the operand stack.
-/

open Aeneas Aeneas.Std Result

namespace Itasca.Wasm2

/-- A block type whose resolved signature is within the limits passes `checkIndex`. -/
theorem checkIndex.complete (env : metadata.Env) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000) :
    checkIndex env bt = .ok (.Ok ()) := by
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
    have hspec : checkIndex env (.TypeIndex index) ⦃ r => r = .Ok () ⦄ := by
      unfold checkIndex
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

/-- A block type whose resolved signature is within the limits passes
`checkBlock`. -/
theorem checkBlock.complete (env : metadata.Env)
    (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
    (hin : resolve env (inputs bt) = some ins) (hout : resolve env (outputs bt) = some outs)
    (hip : ins.length ≤ 1000) (hop : outs.length ≤ 1000) :
    checkBlock env bt = .ok (.Ok ()) := by
  exact checkIndex.complete env bt ins outs hin hout hip hop

/-- Forward realization and exact effects after opening, used by recursive
independent completeness rather than assuming an accepted handler. -/
def EnterForward (st s : code.BodyState) (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (outer segment : List code.StackType) (ts : List valtype) : Prop :=
  ∃ remaining base,
    remaining.length ≤ segment.length ∧ base.val = outer.length + remaining.length ∧
    Sequence.Realizes (Control.polymorphic st.core) remaining ts ∧
    s.core.ctrls.val = st.core.ctrls.val ++ [(Frames.Saved.fresh base form bt ins outs).ctrl] ∧
    s.blocks.val = st.blocks.val ++ [bt] ∧
    s.core.vals.val = outer ++ remaining ++ ins.map code.StackType.Val

/-- A compatible operand segment makes `enterParams` accept and open the frame with effect
`EnterForward`. -/
theorem enterParams.complete (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
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

/-- `enterArgs` also accepts when the stack carries the `i32` condition of `if`. -/
theorem enterArgs.complete (st : code.BodyState) (env : metadata.Env)
    (form : Frames.Form) (bt : signature.BlockType) (ins outs : List wasm_types.ValueType)
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
theorem code.enter.complete (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
     (form : Wasm2.Frames.Form) (initial : form.Initial)
    (bt : signature.BlockType) (next : Usize) (ins outs : List wasm_types.ValueType)
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

end

/-! ## EnterStep -/

section

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

/-- Entry retains the exact supplied parent zipper and decoded callback signature. -/
structure ReaderEnterPost {data env locals index st}
    (p : Pending data env locals index st) (out : code.BodyState)
    (form : Frames.Form) (bt : signature.BlockType)
    (ins outs : List wasm_types.ValueType) (remaining : List code.StackType) (base : Usize) : Prop where
  inputs : resolve env (Wasm2.inputs bt) = some ins
  outputs : resolve env (Wasm2.outputs bt) = some outs
  inputBound : ins.length ≤ 1000
  outputBound : outs.length ≤ 1000
  encoded : At data p.start (form.token bt) out.core.pos
  popped : ∀ ts, Sequence.Realizes p.current.ctrl.polymorphic_base remaining ts →
    Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals (ts ++ form.args ins)
  basePosition : base.val = p.current.ctrl.value_stack_base.val + remaining.length
  opened : Frames.Open env (bodyContext env locals p.ft) out
    (p.parents ++ [{ p.current with vals := remaining }]) (Frames.Saved.fresh base form bt ins outs)
  after : p.After out

/-- Opening a `block`, `loop` or `if` frame with `code.enter` preserves `Pending` on success. -/
theorem Pending.enter_reader {data env locals index st} (p : Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (hbyte : data.val[p.start.val]'p.inbounds = form.opcode) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () → ∃ bt ins outs remaining newBase,
      Wasm2.BlockDecoded data st.core.pos bt r.2.core.pos ∧
      ReaderEnterPost p r.2 form bt ins outs remaining newBase ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hcap : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  apply WP.spec_mono (code.enter.sound st data env form initial outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) p.opened.shape.core hcap)
  intro r hr hok
  obtain ⟨bt, ins, outs, hdecoded, hin, hout, hip, hop, remaining, newBase,
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
  refine ⟨bt, ins, outs, remaining, newBase, hdecoded, hin, hout, hip, hop, encoded,
    (by simpa [Control.polymorphic, ctrls] using hpop),
    (by simpa [base] using hbase), ho, ?_⟩
  refine p.running_after r.2 _ _ (form.token bt) encoded ho ?_ ?_ ?_
    (by cases form <;> simp [Frames.Form.token, Token.Declared])
  · simpa [Frames.bodyType_enter] using p.bodyType
  · have he : form.opening bt = [form.token bt] := by
      rcases initial with rfl | rfl | rfl <;> rfl
    simpa [he] using htrace
  · simp [hblocks]

/-- Opening a `block`, `loop` or `if` frame with `code.enter` preserves `Pending` on success. -/
theorem Pending.enter_after {data env locals index st} (p : Pending data env locals index st)
    (form : Frames.Form) (initial : form.Initial)
    (hbyte : data.val[p.start.val]'p.inbounds = form.opcode) :
    code.enter st data env form.kind ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.enter_reader form initial hbyte)
  intro r effect accepted
  obtain ⟨_, _, _, _, _, _, post⟩ := effect accepted
  exact post.after

end Itasca.Wasm2

end
