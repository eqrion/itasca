import Itasca.Binary.Wasm1.Encoding
import Itasca.Wasm1.Frames
import Itasca.Support.EnvTranslation
import Itasca.Wasm1.Loop

open Aeneas Aeneas.Std

namespace Itasca.Wasm1.Frames

theorem Spine.matches {env ctx parents C outer form}
    (h : Spine (EnvTranslation.context env ctx) parents C outer form) :
    EnvTranslation.Matches env ctx C := by
  induction h with
  | root => exact .root _ _
  | push _ _ _ _ _ _ _ _ _ _ ih => exact ih.enter _

end Itasca.Wasm1.Frames

namespace Itasca.Wasm1

def FunctionTyped (env : module.Env) (ctx : code.Context) (bt : code.BlockType)
    (ops : List instr) : Prop :=
  Instrs_ok (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops
    (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt)))

structure Bounds (data : Slice U8) (st : code.OpIterState) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.pos.val ≤ data.length
  vals : st.vals.val.length ≤ st.pos.val
  ctrls : st.ctrls.val.length ≤ st.pos.val + 1



/-- The invariant records only the bytes already consumed. The unread suffix
may contain arbitrary malformed or unsupported instructions. -/
inductive State (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) : code.OpIterState → Prop where
  | running (st : code.OpIterState) (parents : List Wasm1.Frames.Saved) (current : Wasm1.Frames.Saved) :
      Bounds data st → Wasm1.Frames.Open (EnvTranslation.context env ctx) st parents current →
      Wasm1.Frames.bodyType parents current = some bt →
      Consumed data 0#usize (Wasm1.Frames.trace parents current) st.pos → State data env ctx bt st
  | closed (st : code.OpIterState) (ops : List instr) (tokens : List Token) :
      Bounds data st → st.ctrls.val = [] → BodyTokens tokens ops → FunctionTyped env ctx bt ops →
      Consumed data 0#usize tokens st.pos →
      Wasm1.Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops →
      State data env ctx bt st

theorem State.bounds {data env ctx bt st} (h : State data env ctx bt st) : Bounds data st := by
  cases h <;> assumption

theorem State.finished {data env ctx bt st} (h : State data env ctx bt st)
    (hctrls : st.ctrls.val = []) (hpos : st.pos.val = data.length) :
    ∃ ops, BodyEncoding data ops ∧ FunctionTyped env ctx bt ops ∧
      Wasm1.Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops := by
  cases h with
  | running parents current _ hopen _ _ =>
      obtain ⟨_, _, _, _, _, _, hc, _⟩ := hopen
      simp [hctrls] at hc
  | closed ops tokens _ _ hbody htyped hconsumed hprofile =>
      exact ⟨ops, ⟨tokens, st.pos, hconsumed, hpos, hbody⟩, htyped, hprofile⟩

/-- A pending opcode has been read; its immediate has not been assumed valid. -/
structure Pending (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (st : code.OpIterState) where
  start : Usize
  parents : List Wasm1.Frames.Saved
  current : Wasm1.Frames.Saved
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  opened : Wasm1.Frames.Open (EnvTranslation.context env ctx) st parents current
  bodyType : Wasm1.Frames.bodyType parents current = some bt
  consumed : Consumed data 0#usize (Wasm1.Frames.trace parents current) start
  inbounds : start.val < data.length
  pos : st.pos.val = start.val + 1
  vals : st.vals.val.length ≤ start.val
  ctrls : st.ctrls.val.length ≤ start.val + 1

def Pending.After {data env ctx bt st} (_ : Pending data env ctx bt st)
    (s : code.OpIterState) : Prop :=
  State data env ctx bt s ∧ st.pos.val ≤ s.pos.val ∧ s.pos.val ≤ data.length

theorem Pending.val_capacity {data env ctx bt st} (p : Pending data env ctx bt st) :
    st.vals.val.length + 1 < Usize.max := by
  have := p.size
  have := p.vals
  have := p.inbounds
  have := Body.byte_limit_room
  omega

theorem Pending.ctrl_capacity {data env ctx bt st} (p : Pending data env ctx bt st) :
    st.ctrls.val.length < Usize.max := by
  have := p.size
  have := p.ctrls
  have := p.inbounds
  have := Body.byte_limit_room
  omega

theorem Pending.bounds_after {data env ctx bt st} (p : Pending data env ctx bt st)
    (st' : code.OpIterState) (token : Token) (encoded : At data p.start token st'.pos)
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1)
    (hctrls : st'.ctrls.val.length ≤ st.ctrls.val.length + 1) : Bounds data st' := by
  have := encoded.span
  have := p.vals
  have := p.ctrls
  exact ⟨p.size, encoded.span.2, by omega, by omega⟩

theorem Pending.running_after {data env ctx bt st} (p : Pending data env ctx bt st)
    (st' : code.OpIterState) (parents : List Wasm1.Frames.Saved) (current : Wasm1.Frames.Saved)
    (token : Token) (encoded : At data p.start token st'.pos)
    (hopen : Wasm1.Frames.Open (EnvTranslation.context env ctx) st' parents current)
    (hbody : Wasm1.Frames.bodyType parents current = some bt)
    (htrace : Wasm1.Frames.trace parents current = Wasm1.Frames.trace p.parents p.current ++ [token])
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1)
    (hctrls : st'.ctrls.val.length ≤ st.ctrls.val.length + 1) : p.After st' := by
  refine ⟨.running st' parents current (p.bounds_after st' token encoded hvals hctrls)
    hopen hbody ?_, ?_, encoded.span.2⟩
  · rw [htrace]
    exact .snoc p.consumed encoded
  · have := encoded.span
    have := p.pos
    omega

theorem Pending.closed_after {data env ctx bt st} (p : Pending data env ctx bt st)
    (st' : code.OpIterState) (ops : List instr) (encoded : At data p.start .end_ st'.pos)
    (hctrls : st'.ctrls.val = [])
    (hbody : BodyTokens (Wasm1.Frames.trace p.parents p.current ++ [.end_]) ops)
    (htyped : FunctionTyped env ctx bt ops)
    (hprofile : Wasm1.Instructions (Wasm1.Frames.enter (EnvTranslation.context env ctx) .body bt) ops)
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1) : p.After st' := by
  refine ⟨.closed st' ops (Wasm1.Frames.trace p.parents p.current ++ [.end_])
    (p.bounds_after st' .end_ encoded hvals (by simp [hctrls])) hctrls hbody htyped
    (.snoc p.consumed encoded) hprofile, ?_, encoded.span.2⟩
  have := encoded.span
  have := p.pos
  omega

/-- Append a typed leaf at the actual current context, including its decoded bytes. -/
theorem Pending.append_result {data env ctx bt st} (p : Pending data env ctx bt st)
    (C : context) (outer : List code.StackType)
    (spine : Wasm1.Frames.Spine (EnvTranslation.context env ctx) p.parents C outer p.current.form)
    (header : Wasm1.Frames.Header C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (ctrls : st.ctrls.val = p.parents.map Wasm1.Frames.Saved.ctrl ++ [p.current.ctrl])
    (vals : st.vals.val = outer ++ p.current.vals)
    (s : code.OpIterState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : At data p.start (.plain op) s.pos)
    (typed : Sequence.TypedPrefix (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.ctrls.val = p.parents.map Wasm1.Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hv : s.vals.val = outer ++ newVals)
    (hlen : newVals.length ≤ p.current.vals.length + 1)
    (hprofile : Wasm1.Instruction (Wasm1.Frames.enter C p.current.form p.current.ctrl.block_type) op := by exact .leaf _ _ (by trivial)) : p.After s := by
  refine p.running_after s p.parents (p.current.advance (.plain op) op poly newVals)
    (.plain op) encoded ?_ ?_ ?_ ?_ ?_
  · exact ⟨C, outer, spine, ⟨header.kind, header.prior, .simple header.emits (.plain op hwf),
        header.profile.append (.cons hprofile (.nil _)), header.priorProfile⟩,
      base, typed, hc, hv⟩
  · simpa [Wasm1.Frames.bodyType_advance] using p.bodyType
  · simp [Wasm1.Frames.trace, Wasm1.Frames.Saved.trace, Wasm1.Frames.Saved.advance, List.append_assoc]
  · simp only [hv, vals, List.length_append]
    omega
  · simp [hc, ctrls]

/-- Context-independent leaf rules also compose through the same invariant. -/
theorem Pending.append_simple {data env ctx bt st} (p : Pending data env ctx bt st)
    (st' : code.OpIterState) (op : instr) (poly : Bool) (vals : List code.StackType)
    (hwf : wf_instr op) (encoded : At data p.start (.plain op) st'.pos)
    (htyped : ∀ C, wf_context C →
      Sequence.TypedPrefix C p.current.ops p.current.ctrl.polymorphic_base p.current.vals →
      Sequence.TypedPrefix C (p.current.ops ++ [op]) poly vals)
    (hctrls : st'.ctrls.val = p.parents.map Wasm1.Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hvals : st'.vals.val = st.vals.val.take p.current.ctrl.value_stack_base.val ++ vals)
    (hlen : vals.length ≤ p.current.vals.length + 1)
    (hprofile : ∀ C, Wasm1.Instruction C op := by intro C; exact .leaf _ _ (by trivial)) : p.After st' := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, stack⟩ := id p.opened
  apply p.append_result C outer spine header base ctrls stack st' op poly vals hwf encoded
    (htyped _ (Wasm1.Frames.enter_wf _ (spine.context_wf (EnvTranslation.context_wf env ctx)) _ _) typed)
    hctrls _ hlen (hprofile _)
  simpa [stack, base] using hvals

end Itasca.Wasm1
