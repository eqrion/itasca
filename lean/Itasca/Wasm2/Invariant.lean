import Itasca.Wasm2.BodySpec
import Itasca.Wasm2.ProfileFrames
import Itasca.Wasm2.ProfileFilters

/-!
# Body loop invariant

The invariant of the extracted body loop. `State` says that the loop state is a running typed
frame zipper (`Frames.Open`) or a completed typed body, with exact provenance for the consumed
bytes. For Wasm 1.0 it also carries the Wasm 1.0 grammar for the consumed bytes and the
`Frames.ProfileFrames` restrictions. `Pending` is the state just after an opcode byte that passed
the profile's opcode filter is read, and `Pending.After` is the postcondition that every
per-opcode handler proves. `Pending.finish_body` and `Pending.append_result` are the shared steps
for closing the body and appending results.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Implementation limits on the body size, the byte cursor and the number of open frames. -/
structure Bounds (data : Slice U8) (st : code.BodyState) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.core.pos.val ≤ data.length
  ctrls : st.blocks.val.length ≤ st.core.pos.val + 1

/-- A running typed zipper or a completed typed body, with exact provenance
for the consumed prefix. No condition is placed on unread bytes. -/
inductive State (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) : code.BodyState → Prop where
  | running (st : code.BodyState) (ft : wasm_types.FuncType)
      (parents : List Frames.Saved) (current : Frames.Saved) :
      env.types.val[index.val]? = some ft → Bounds data st →
      Frames.Open env (bodyContext env locals ft) st parents current →
      Frames.bodyType parents current = some (.TypeIndex index) →
      Consumed data 0#usize (Frames.trace parents current) st.core.pos →
      TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (Frames.trace parents current) →
      Frames.ProfileFrames profile (bodyContext env locals ft) (parents ++ [current]) →
      (profile = .Wasm1 → Wasm1.Consumed data 0#usize (Frames.trace parents current) st.core.pos) →
      State data env profile locals index st
  | closed (st : code.BodyState) (ft : wasm_types.FuncType) (ops : List instr) (tokens : List Token) :
      env.types.val[index.val]? = some ft → Bounds data st →
      st.core.ctrls.val = [] → st.blocks.val = [] → BodyTokens tokens ops →
      FunctionTyped env locals ft ops → Consumed data 0#usize tokens st.core.pos →
      TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) tokens →
      (profile = .Wasm1 → Wasm1.Instructions (functionContext env locals ft) ops) →
      (profile = .Wasm1 → Wasm1.Consumed data 0#usize tokens st.core.pos) →
      State data env profile locals index st

theorem State.bounds {data env profile locals index st} (h : State data env profile locals index st) :
    Bounds data st := by cases h <;> assumption

theorem State.shape {data env profile locals index st} (h : State data env profile locals index st) :
    Shape st := by
  cases h with
  | running ft parents current hi bounds ho hb hc hd => exact ho.shape
  | closed _ _ _ _ _ hc hb _ _ _ _ =>
    exact ⟨⟨by simp [hc], by simp [hc]⟩, by simp [hc, hb]⟩

theorem State.finished {data env profile locals index st}
    (h : State data env profile locals index st)
    (hblocks : st.blocks.val = []) (hpos : st.core.pos.val = data.length) :
    Validated profile data env locals index := by
  cases h with
  | running ft parents current _ _ ho _ _ _ =>
    obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := ho
    simp [hblocks] at hb
  | closed ft ops tokens hi _ _ _ ht htyped hc hd hinstrs hwasm1 =>
    exact ⟨ft, ops, hi, ⟨tokens, st.core.pos, hc, hpos, ht⟩, htyped, (ht.declared_iff _).mp hd,
      fun hp => ⟨⟨tokens, st.core.pos, hwasm1 hp, hpos, ht⟩, hinstrs hp⟩⟩

/-- The loop's initial body state: one body frame for the function type at `index`. -/
def initial (index : U32) : code.BodyState :=
  { core := ⟨alloc.vec.Vec.new _,
      alloc.vec.Vec.from [⟨.Body, .TypeIndex index, 0#usize, false⟩] (by scalar_tac), 0#usize⟩ }

/-- The initial state satisfies `State` for a body within the size limit. -/
theorem State.start (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (index : U32) (ft : wasm_types.FuncType) (hi : env.types.val[index.val]? = some ft)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    State data env profile locals index (initial index) := by
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
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening]
  · exact Frames.ProfileFrames.start profile _ _ _ _ _
  · intro _
    simpa [Frames.trace, Frames.Saved.trace, Frames.Saved.fresh, Frames.Form.opening, initial]
      using Wasm1.Consumed.nil (data := data) 0#usize (by simp)

/-- The opcode has been consumed and passed the profile's opcode filter, but its immediate is
still arbitrary. -/
structure Pending (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (locals : alloc.vec.Vec wasm_types.ValueType) (index : U32) (st : code.BodyState) where
  start : Usize
  ft : wasm_types.FuncType
  parents : List Frames.Saved
  current : Frames.Saved
  signature : env.types.val[index.val]? = some ft
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  opened : Frames.Open env (bodyContext env locals ft) st parents current
  bodyType : Frames.bodyType parents current = some (.TypeIndex index)
  consumed : Consumed data 0#usize (Frames.trace parents current) start
  declared : TokensDeclared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) (Frames.trace parents current)
  inbounds : start.val < data.length
  pos : st.core.pos.val = start.val + 1
  ctrls : st.blocks.val.length ≤ start.val + 1
  profileFrames : Frames.ProfileFrames profile (bodyContext env locals ft) (parents ++ [current])
  profileConsumed : profile = .Wasm1 →
    Wasm1.Consumed data 0#usize (Frames.trace parents current) start
  opcode : profile = .Wasm1 → (data.val[start.val]'inbounds).val ∉ Wasm1.extensionOpcodes

/-- A running state with bytes left yields a `Pending` after reading one opcode byte that passes
the profile's opcode filter. -/
theorem State.pending {data env profile locals index st}
    (h : State data env profile locals index st)
    (hblocks : st.blocks.val ≠ []) (hpos : st.core.pos.val < data.length)
    (hop : profile = .Wasm1 → (data.val[st.core.pos.val]'hpos).val ∉ Wasm1.extensionOpcodes)
    (next : Usize) (hnext : next.val = st.core.pos.val + 1) :
    ∃ p : Pending data env profile locals index { st with core := { st.core with pos := next } },
      p.start = st.core.pos := by
  cases h with
  | closed _ _ _ _ _ _ hb _ _ _ _ _ _ => exact False.elim (hblocks hb)
  | running ft parents current hi bounds ho hbody hc hd hframes hwasm1 =>
    exact ⟨⟨st.core.pos, ft, parents, current, hi, bounds.size, ho.with_pos next, hbody,
      hc, hd, hpos, hnext, bounds.ctrls, hframes, hwasm1, hop⟩, rfl⟩

/-- The postcondition of one opcode step: the resulting state satisfies `State` and its cursor has
advanced within the data. -/
def Pending.After {data env profile locals index st} (_ : Pending data env profile locals index st)
    (s : code.BodyState) : Prop :=
  State data env profile locals index s ∧ st.core.pos.val ≤ s.core.pos.val ∧
    s.core.pos.val ≤ data.length

/-- Under Wasm 1.0, a token whose opcode is not `call_indirect` and whose block type has a
one-byte spelling is a Wasm 1.0 token. -/
theorem Pending.wasm1_at {data env profile locals index st}
    (p : Pending data env profile locals index st) {token : Token} {next : Usize}
    (encoded : At data p.start token next)
    (hindirect : data.val[p.start.val]'p.inbounds ≠ 0x11#u8)
    (hblock : Wasm1.BlockTokenOk token := by trivial) :
    profile = .Wasm1 → Wasm1.At data p.start token next := fun hp =>
  Wasm1.At.of_wasm2 encoded p.inbounds (p.opcode hp) hindirect hblock

/-- The opcode of a `Pending` state passes the profile's opcode filter. -/
theorem Pending.check_opcode {data env profile locals index st}
    (p : Pending data env profile locals index st) :
    code.check_opcode profile (data.val[p.start.val]'p.inbounds) = .ok (.Ok ()) := by
  cases profile with
  | Wasm1 => exact code.check_opcode.complete _ _ (p.opcode rfl)
  | Wasm2 => rfl

/-- An extension opcode cannot reach a Wasm 1.0 step. -/
theorem Pending.not_wasm1 {data env profile locals index st}
    (p : Pending data env profile locals index st) {opcode : U8}
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hext : opcode.val ∈ Wasm1.extensionOpcodes) : profile ≠ .Wasm1 := fun hp =>
  p.opcode hp (hbyte ▸ hext)

theorem Pending.running_after {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (s : code.BodyState) (parents : List Frames.Saved) (current : Frames.Saved)
    (token : Token) (encoded : At data p.start token s.core.pos)
    (ho : Frames.Open env (bodyContext env locals p.ft) s parents current)
    (hb : Frames.bodyType parents current = some (.TypeIndex index))
    (ht : Frames.trace parents current = Frames.trace p.parents p.current ++ [token])
    (hc : s.blocks.val.length ≤ st.blocks.val.length + 1)
    (hframes : Frames.ProfileFrames profile (bodyContext env locals p.ft) (parents ++ [current]))
    (hwasm1 : profile = .Wasm1 → Wasm1.At data p.start token s.core.pos)
    (hd : token.Declared (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) := by
      simp [Token.Declared, DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  have hbnd := p.ctrls
  refine ⟨.running s p.ft parents current p.signature
    ⟨p.size, hs.2, by omega⟩ ho hb ?_ ?_ hframes ?_, by omega, hs.2⟩
  · rw [ht]
    exact .snoc p.consumed encoded
  · rw [ht, tokensDeclared_append, tokensDeclared_singleton]
    exact ⟨p.declared, hd⟩
  · intro hp
    rw [ht]
    exact .snoc (p.profileConsumed hp) (hwasm1 hp)

theorem Pending.closed_after {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (s : code.BodyState) (ops : List instr) (encoded : At data p.start .end_ s.core.pos)
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = [])
    (ht : BodyTokens (Frames.trace p.parents p.current ++ [.end_]) ops)
    (htyped : FunctionTyped env locals p.ft ops)
    (hinstrs : profile = .Wasm1 → Wasm1.Instructions (functionContext env locals p.ft) ops)
    (hwasm1 : profile = .Wasm1 → Wasm1.At data p.start .end_ s.core.pos) : p.After s := by
  have hs := encoded.span
  have hp := p.pos
  exact ⟨.closed s p.ft ops _ p.signature ⟨p.size, hs.2, by simp [hb]⟩ hc hb ht htyped
    (.snoc p.consumed encoded) (by simpa [Token.Declared] using p.declared) hinstrs
    (fun hp => .snoc (p.profileConsumed hp) (hwasm1 hp)), by omega, hs.2⟩

/-- Closing the root frame recovers the result vector selected by the actual
function type index, without treating function parameters as operands. -/
theorem Pending.finish_body {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (s : code.BodyState) (encoded : At data p.start .end_ s.core.pos)
    (hbyte : data.val[p.start.val]'p.inbounds = 0x0B#u8)
    (hform : p.current.form = .body)
    (hresults : Sequence.Realizes p.current.ctrl.polymorphic_base p.current.vals
      (p.current.outs.map Translate.valueType))
    (hc : s.core.ctrls.val = []) (hb : s.blocks.val = []) : p.After s := by
  obtain ⟨hparents, htokens, htyped⟩ := p.opened.finish_body hform hresults
  have hbt : p.current.bt = .TypeIndex index := by simpa [hparents] using p.bodyType
  have hframes := p.profileFrames
  rw [hparents] at hframes
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
  have hr : p.current.outs = p.ft.results.val := by
    have ho := header.outputs
    simpa [hbt, outputs, resolve, p.signature] using ho.symm
  apply p.closed_after s p.current.ops encoded hc hb htokens
  · simpa [FunctionTyped, functionContext, Frames.enter, Frames.Form.label, hr] using htyped
  · intro hp
    simpa [functionContext, hr] using hframes.finish hform hp
  · exact p.wasm1_at encoded (by rw [hbyte]; decide)

/-- Shared leaf preservation uses arbitrary frame inputs, while retaining the
same descriptor and exact byte provenance. Calls may append multiple values. -/
theorem Pending.append_result {data env profile locals index st}
    (p : Pending data env profile locals index st)
    (C : context) (outer : List code.StackType)
    (spine : Frames.Spine env (bodyContext env locals p.ft) p.parents C outer
      p.current.form p.current.ins)
    (header : Frames.Header env C p.current)
    (base : p.current.ctrl.value_stack_base.val = outer.length)
    (s : code.BodyState) (op : instr) (poly : Bool) (newVals : List code.StackType)
    (hwf : wf_instr op) (encoded : At data p.start (.plain op) s.core.pos)
    (typed : TypedPrefix (Frames.enter C p.current.form p.current.ins p.current.outs)
      ((p.current.form.params p.current.ins).map Translate.valueType)
      (p.current.ops ++ [op]) poly newVals)
    (hc : s.core.ctrls.val = p.parents.map Frames.Saved.ctrl ++
      [{ p.current.ctrl with polymorphic_base := poly }])
    (hb : s.blocks.val = p.parents.map Frames.Saved.bt ++ [p.current.bt])
    (hv : s.core.vals.val = outer ++ newVals)
    (hwasm1 : profile = .Wasm1 → Wasm1.At data p.start (.plain op) s.core.pos ∧
      Wasm1.Instruction (Frames.enter C p.current.form p.current.ins p.current.outs) op)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op := by
      simp [DeclaredReferences.Instruction, DeclaredReferences.instructionIndices]) : p.After s := by
  refine p.running_after s p.parents (p.current.advance (.plain op) op poly newVals)
    (.plain op) encoded ?_ ?_ ?_ ?_ ?_ (fun hp => (hwasm1 hp).1) hdecl
  · exact ⟨C, outer, spine, ⟨header.kind, header.inputs, header.outputs,
      header.prior, .simple header.emits (.plain op hwf)⟩, base, typed, hc, hb, hv⟩
  · simpa [Frames.bodyType_advance] using p.bodyType
  · simp [Frames.trace, Frames.Saved.trace, Frames.Saved.advance, List.append_assoc]
  · obtain ⟨_, _, _, _, _, _, _, hblocks, _⟩ := p.opened
    simp [hb, hblocks]
  · exact p.profileFrames.advance _ (by simp [Frames.enter, spine.labels, Frames.labels_snoc])
      (.plain op) op poly newVals (fun hp => (hwasm1 hp).2)

end Itasca.Wasm2

namespace Itasca

/-- `Wasm2.initial` is exactly the state `code.push_frame` builds for the body frame. -/
theorem code.push_frame.initial (index : U32) :
    code.push_frame
      { core := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _, 0#usize⟩ } .Body (.TypeIndex index) =
      .ok (Wasm2.initial index) := by
  simp [code.push_frame, Wasm2.initial, alloc.vec.Vec.push, U32.max, U32.numBits]
  rfl

end Itasca
