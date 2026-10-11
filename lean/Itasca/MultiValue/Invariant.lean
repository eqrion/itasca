import Itasca.MultiValue.Frames

open Aeneas Aeneas.Std

namespace Itasca.MultiValue

/-- Return typing comes from the selected type-section entry. The runtime's
shared scalar context carries empty results because return is dispatched by
the multi-value loop itself. Function parameters are already included in locals. -/
def bodyContext (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) : context := EnvTranslation.context env ⟨locals, ft.results⟩

def FunctionTyped (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (ft : types.FuncType) (ops : List instr) : Prop :=
  Instrs_ok (Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft)
    ops (.mk_functype (.mk_list []) (.mk_list (ft.results.val.map Translate.valueType)))

/-- Intended whole-body soundness/completeness certificate. It contains no
validator-success premise and imposes no Wasm 1.0 result-arity restriction. -/
def Validated (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (index : U32) : Prop :=
  ∃ ft ops, env.types.val[index.val]? = some ft ∧ BodyEncoding data ops ∧
    FunctionTyped env locals ft ops

structure Bounds (data : Slice U8) (st : multi_value.State) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.core.pos.val ≤ data.length
  ctrls : st.blocks.val.length ≤ st.core.pos.val + 1

/-- A running typed zipper or a completed typed body, with exact provenance
for the consumed prefix. No condition is placed on unread bytes. -/
inductive State (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (index : U32) : multi_value.State → Prop where
  | running (st : multi_value.State) (ft : types.FuncType)
      (parents : List Frames.Saved) (current : Frames.Saved) :
      env.types.val[index.val]? = some ft → Bounds data st →
      Frames.Open env (bodyContext env locals ft) st parents current →
      Frames.bodyType parents current = some (.TypeIndex index) →
      Consumed data 0#usize (Frames.trace parents current) st.core.pos → State data env locals index st
  | closed (st : multi_value.State) (ft : types.FuncType) (ops : List instr) (tokens : List Token) :
      env.types.val[index.val]? = some ft → Bounds data st →
      st.core.ctrls.val = [] → st.blocks.val = [] → BodyTokens tokens ops →
      FunctionTyped env locals ft ops → Consumed data 0#usize tokens st.core.pos →
      State data env locals index st

theorem State.bounds {data env locals index st} (h : State data env locals index st) :
    Bounds data st := by cases h <;> assumption

theorem State.shape {data env locals index st} (h : State data env locals index st) : Shape st := by
  cases h with
  | running ft parents current hi bounds ho hb hc => exact ho.shape
  | closed _ _ _ _ _ hc hb _ _ _ =>
    exact ⟨⟨by simp [hc], by simp [hc]⟩, by simp [hc, hb]⟩

theorem State.finished {data env locals index st} (h : State data env locals index st)
    (hblocks : st.blocks.val = []) (hpos : st.core.pos.val = data.length) :
    Validated data env locals index := by
  cases h with
  | running ft parents current _ _ ho _ _ =>
    obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := ho
    simp [hblocks] at hb
  | closed ft ops tokens hi _ _ _ ht htyped hc =>
    exact ⟨ft, ops, hi, ⟨tokens, st.core.pos, hc, hpos, ht⟩, htyped⟩

def initial (index : U32) : multi_value.State :=
  { core := ⟨alloc.vec.Vec.new _,
      alloc.vec.Vec.from [⟨.Body, .Empty, .TypeIndex index, 0#usize, false⟩] (by scalar_tac), 0#usize⟩ }

theorem State.start (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (index : U32) (ft : types.FuncType) (hi : env.types.val[index.val]? = some ft)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data env locals index (initial index) := by
  apply State.running (initial index) ft []
    (Frames.Saved.fresh 0#usize .body (.TypeIndex index) ft.params.val ft.results.val) hi
  · constructor <;> simp [initial, hsize]
  · apply Frames.Open.start env _ (EnvTranslation.context_wf env ⟨locals, ft.results⟩)
    · simp [resolve, inputs, hi]
    · simp [resolve, outputs, hi]
    · rfl
    · rfl
    · rfl
  · rfl
  · simpa [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening, initial]
      using Consumed.nil (data := data) 0#usize (by simp)

/-- The opcode has been consumed, but its immediate is still arbitrary. -/
structure Pending (data : Slice U8) (env : module.Env) (locals : alloc.vec.Vec types.ValueType)
    (index : U32) (st : multi_value.State) where
  start : Usize
  ft : types.FuncType
  parents : List Frames.Saved
  current : Frames.Saved
  signature : env.types.val[index.val]? = some ft
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  opened : Frames.Open env (bodyContext env locals ft) st parents current
  bodyType : Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Consumed data 0#usize (Frames.trace parents current) start
  inbounds : start.val < data.length
  pos : st.core.pos.val = start.val + 1
  ctrls : st.blocks.val.length ≤ start.val + 1

theorem State.pending {data env locals index st} (h : State data env locals index st)
    (hblocks : st.blocks.val ≠ []) (hpos : st.core.pos.val < data.length)
    (next : Usize) (hnext : next.val = st.core.pos.val + 1) :
    ∃ p : Pending data env locals index { st with core := { st.core with pos := next } },
      p.start = st.core.pos := by
  cases h with
  | closed _ _ _ _ _ _ hb _ _ _ => exact False.elim (hblocks hb)
  | running ft parents current hi bounds ho hbody hc =>
    exact ⟨⟨st.core.pos, ft, parents, current, hi, bounds.size, ho.with_pos next, hbody,
      hc, hpos, hnext, bounds.ctrls⟩, rfl⟩

def Pending.After {data env locals index st} (_ : Pending data env locals index st)
    (s : multi_value.State) : Prop :=
  State data env locals index s ∧ st.core.pos.val ≤ s.core.pos.val ∧ s.core.pos.val ≤ data.length

theorem Pending.running_after {data env locals index st} (p : Pending data env locals index st)
    (s : multi_value.State) (parents : List Frames.Saved) (current : Frames.Saved)
    (token : Token) (encoded : At data p.start token s.core.pos)
    (ho : Frames.Open env (bodyContext env locals p.ft) s parents current)
    (hb : Frames.bodyType parents current = some (.TypeIndex index))
    (ht : Frames.trace parents current = Frames.trace p.parents p.current ++ [token])
    (hc : s.blocks.val.length ≤ st.blocks.val.length + 1) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  have hbnd := p.ctrls
  refine ⟨.running s p.ft parents current p.signature
    ⟨p.size, hs.2, by omega⟩ ho hb ?_, by omega, hs.2⟩
  rw [ht]
  exact .snoc p.consumed encoded

theorem Pending.closed_after {data env locals index st} (p : Pending data env locals index st)
    (s : multi_value.State) (ops : List instr) (encoded : At data p.start .end_ s.core.pos)
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = [])
    (ht : BodyTokens (Frames.trace p.parents p.current ++ [.end_]) ops)
    (htyped : FunctionTyped env locals p.ft ops) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  exact ⟨.closed s p.ft ops _ p.signature ⟨p.size, hs.2, by simp [hb]⟩ hc hb ht htyped
    (.snoc p.consumed encoded), by omega, hs.2⟩

/-- Closing the root frame recovers the result vector selected by the actual
function type index, without treating function parameters as operands. -/
theorem Pending.finish_body {data env locals index st} (p : Pending data env locals index st)
    (s : multi_value.State) (encoded : At data p.start .end_ s.core.pos)
    (hform : p.current.form = .body)
    (hresults : Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
      (p.current.outs.map Translate.valueType))
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = []) : p.After s := by
  obtain ⟨hparents, htokens, htyped⟩ := p.opened.finish_body hform hresults
  have hbt : p.current.bt = .TypeIndex index := by simpa [hparents] using p.bodyType
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hr : p.current.outs = p.ft.results.val := by
    have ho := header.outputs
    simpa [hbt, outputs, resolve, p.signature] using ho.symm
  apply p.closed_after s p.current.ops encoded hc hb htokens
  simpa [FunctionTyped, Frames.enter, Frames.Form.label, hr] using htyped

/-- Shared leaf preservation uses arbitrary frame inputs, while retaining the
same descriptor and exact byte provenance. Calls may append multiple values. -/
theorem Pending.append_result {data env locals index st} (p : Pending data env locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer
      p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (s : multi_value.State) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : At data p.start (.plain op) s.core.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hb : s.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (hv : s.core.vals.val = outer ++ newVals) : p.After s := by
  refine p.running_after s p.parents (p.current.advance (.plain op) op poly newVals)
    (.plain op) encoded ?_ ?_ ?_ ?_
  · exact ⟨C, outer, spine, ⟨header.kind, header.placeholder, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain op hwf)⟩, base, typed, hc, hb, hv⟩
  · simpa [Frames.bodyType_advance] using p.bodyType
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.advance, List.append_assoc]
  · obtain ⟨_, _, _, _, _, _, _, hblocks, _⟩ := p.opened
    simp [hb, hblocks]

end Itasca.MultiValue

namespace Itasca

/-- The ghost initial state is exactly the extracted frame initialization. -/
theorem multi_value.push_frame.initial (index : U32) :
    multi_value.push_frame
      { core := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _, 0#usize⟩ } .Body (.TypeIndex index) =
      .ok (MultiValue.initial index) := by
  simp [multi_value.push_frame, code.push_ctrl, MultiValue.initial,
    alloc.vec.Vec.push, U32.max, U32.numBits]
  rfl

end Itasca
