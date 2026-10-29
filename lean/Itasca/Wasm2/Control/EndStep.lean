import Itasca.Wasm2.Control.EndComplete

/-!
# `end` and `else` step

`Pending.end_after` shows that `code.end_frame` for `else` (`0x05`) and `end` (`0x0b`) preserves
`Pending`, by closing the child frame into its suspended parent or, for the body frame, finishing
the function.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

private theorem empty_spine_form {env root parents C outer form ins}
    (h : Frames.Spine env root parents C outer form ins) (he : parents = []) : form = .body := by
  cases h with
  | root => rfl
  | push => simp at he

/-- Exact child-to-parent source resumption on a non-root `end`. -/
def resumedSource (parent child : Frames.Saved) (instruction : instr) : Frames.Saved :=
  { parent with
    ops := parent.ops ++ [instruction]
    vals := parent.vals ++ child.outs.map code.StackType.Val
    tokens := parent.tokens ++ child.trace ++ [.end_] }

/-- The supplied source zipper after END, including the root completion alternative. -/
def ReaderEndZipper {data env profile locals index st}
    (p : Pending data env profile locals index st) (out : code.BodyState) : Prop :=
  (p.current.form = .body ∧ p.parents = [] ∧
    BodyTokens (Frames.trace p.parents p.current ++ [.end_]) p.current.ops ∧
    Instrs_ok (Frames.enter (bodyContext env locals p.ft) .body p.current.ins p.current.outs)
      p.current.ops (.mk_functype (.mk_list []) (.mk_list (p.current.outs.map Translate.valueType)))) ∨
  ∃ grandparents parent instruction, p.parents = grandparents ++ [parent] ∧
    Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
    Frames.Open env (bodyContext env locals p.ft) out grandparents
      (resumedSource parent p.current instruction)

/-- Exact source resumption and operand results for either closing handler. -/
def ReaderClosePost {data env profile locals index st}
    (p : Pending data env profile locals index st) (out : code.BodyState) (isElse : Bool) : Prop :=
  if isElse then
    p.current.form = .then_ ∧ At data p.start .else_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧
      Frames.Open env (bodyContext env locals p.ft) out p.parents p.current.nextElse ∧ p.After out
  else
    At data p.start .end_ out.core.pos ∧
      Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
        (p.current.outs.map Translate.valueType) ∧ ReaderEndZipper p out ∧ p.After out

/-- The actual closing handlers preserve the independent typed zipper. -/
theorem Pending.end_reader {data env profile locals index st} (p : Pending data env profile locals index st)
    (isElse : Bool) (opcode : U8) (hop : opcode = if isElse then 0x05#u8 else 0x0B#u8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () → ReaderClosePost p r.2 isElse ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  apply WP.spec_mono (code.end_frame.sound st env isElse
    (p.parents.map Frames.Saved.ctrl) (p.parents.map Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core)
  intro r hr hok
  obtain ⟨allowed, hres, hpos, effect⟩ := hr hok
  have hroot := EnvTranslation.context_wf env ⟨locals, p.ft.results⟩
  have htypes : (bodyContext env locals p.ft).TYPES = env.types.val.map EnvTranslation.funcType := rfl
  have htake : st.core.vals.val.take p.current.ctrl.value_stack_base.val = outer := by
    rw [vals, base, List.take_left]
  cases isElse
  · have encoded : At data p.start .end_ r.2.core.pos := by
      apply At.of_immediate p.inbounds (by simpa [hop] using hbyte) p.pos Immediate.end_
      exact ⟨by simp [hpos], by simp [hpos], by have hp := p.pos; have hi := p.inbounds; rw [hpos]; omega⟩
    obtain ⟨hc, hb, hv⟩ := effect
    have hthen : p.current.form = .then_ → p.current.ins = p.current.outs := by
      intro hf
      exact allowed (by simpa [hf, Frames.Form.kind] using header.kind)
    cases hf : p.current.form with
    | body =>
      have hp : p.parents = [] := (p.opened.finish_body hf hres).1
      refine ⟨encoded, hres, .inl ⟨hf, hp, (p.opened.finish_body hf hres).2⟩, ?_⟩
      exact p.finish_body r.2 encoded (by simpa [hop] using hbyte) hf hres (by simpa [hp] using hc) (by simpa [hp] using hb)
    | block | loop | then_ | else_ thenTokens thenOps =>
      all_goals
        have closed : ∃ op, Frames.Closed p.current.form p.current.bt p.current.ops op := by
          rw [hf]; first | exact ⟨_, .block _ _⟩ | exact ⟨_, .loop _ _⟩ |
            exact ⟨_, .then_ _ _⟩ | exact ⟨_, .else_ _ _ _ _⟩
        obtain ⟨op, closed⟩ := closed
        have hn : p.parents ≠ [] := by
          intro he
          have hf' := empty_spine_form spine he
          simp_all
        obtain ⟨gps, parent, he, ho, htrace⟩ := p.opened.close hroot htypes op closed hres hthen hc hb
          (by simpa [htake, List.map_eq_nil_iff, hn] using hv)
        have hframes := p.profileFrames
        rw [he] at hframes
        refine ⟨encoded, hres, .inr ⟨gps, parent, op, he, closed, ho⟩, ?_⟩
        refine p.running_after r.2 gps _ .end_ encoded ho ?_ htrace ?_
          (hframes.close closed header.inputs header.outputs _ _)
          (p.wasm1_at encoded (by rw [hbyte, hop]; decide))
        · simpa [List.append_assoc] using (Frames.bodyType_close gps parent p.current op).trans
            (by simpa [← he] using p.bodyType)
        · simp [hb, blocks]; omega
  · have hform : p.current.form = .then_ := by
      have hk := header.kind
      have ha : p.current.ctrl.kind = .Then := allowed
      cases hf : p.current.form <;> simp_all [Frames.Form.kind]
    obtain ⟨hc, hb, hv⟩ := effect
    have encoded : At data p.start .else_ r.2.core.pos := by
      apply At.of_immediate p.inbounds (by simpa [hop] using hbyte) p.pos Immediate.else_
      exact ⟨by simp [hpos], by simp [hpos], by have hp := p.pos; have hi := p.inbounds; rw [hpos]; omega⟩
    obtain ⟨ho, ht⟩ := p.opened.else_ hroot hform hres (by simpa [Frames.Saved.nextElse] using hc)
      hb (by simpa [htake] using hv)
    refine ⟨hform, encoded, hres, ho, ?_⟩
    refine p.running_after r.2 p.parents p.current.nextElse .else_ encoded ho ?_ ht ?_
      (p.profileFrames.else_ hform) (p.wasm1_at encoded (by rw [hbyte, hop]; decide))
    · simpa [Frames.bodyType_else] using p.bodyType
    · simp [hb]

/-- The actual closing handlers preserve the independent typed zipper. -/
theorem Pending.end_after {data env profile locals index st} (p : Pending data env profile locals index st)
    (isElse : Bool) (opcode : U8) (hop : opcode = if isElse then 0x05#u8 else 0x0B#u8)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    code.end_frame st env isElse ⦃ r => r.1 = .Ok () → p.After r.2 ⦄ := by
  apply WP.spec_mono (p.end_reader isElse opcode hop hbyte)
  intro r effect accepted
  have post := effect accepted
  cases isElse
  · exact post.2.2.2
  · exact post.2.2.2.2

end Itasca.Wasm2
