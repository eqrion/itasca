import Itasca.Body
import Itasca.CoreBinary
import Itasca.Frames

open Aeneas Aeneas.Std

namespace Itasca.Core

/-- The profile uses no environment-dependent instructions. Locals and the
declared function results retain their usual specification context entries. -/
def functionContext (ctx : code.Context) : context :=
  ⟨[], [], [], [], [], [], [], ctx.locals.val.map Translate.valueType, [],
    some (.mk_list (ctx.results.val.map Translate.valueType))⟩

theorem functionContext_wf (ctx : code.Context) : wf_context (functionContext ctx) := by
  constructor <;> simp [Forall]

def FunctionTyped (ctx : code.Context) (bt : code.BlockType) (ops : List instr) : Prop :=
  Instrs_ok (Frames.enter (functionContext ctx) .body bt) ops
    (.mk_functype (.mk_list []) (.mk_list (Control.resultTypes bt)))

/-- Each consumed opcode can add at most one operand and one control frame. -/
structure Bounds (data : Slice U8) (st : code.OpIterState) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.pos.val ≤ data.length
  vals : st.vals.val.length ≤ st.pos.val
  ctrls : st.ctrls.val.length ≤ st.pos.val + 1

/-- A completed outer frame retains the complete syntax/typing witness even
when trailing bytes still remain for the public driver to reject. -/
inductive State (data : Slice U8) (tokens : List Token) (ctx : code.Context)
    (bt : code.BlockType) : code.OpIterState → Prop where
  | running (st : code.OpIterState) (parents : List Frames.Saved) (current : Frames.Saved)
      (remaining : List Token) :
      Bounds data st → Frames.Open (functionContext ctx) st parents current →
      Frames.bodyType parents current = some bt →
      Rest data st.pos remaining → tokens = Frames.trace parents current ++ remaining →
      State data tokens ctx bt st
  | closed (st : code.OpIterState) (ops : List instr) (done remaining : List Token) :
      Bounds data st → st.ctrls.val = [] → BodyTokens done ops → FunctionTyped ctx bt ops →
      Rest data st.pos remaining → tokens = done ++ remaining →
      State data tokens ctx bt st

theorem State.bounds {data tokens ctx bt st} (h : State data tokens ctx bt st) : Bounds data st := by
  cases h <;> assumption

theorem State.finished {data tokens ctx bt st} (h : State data tokens ctx bt st)
    (hctrls : st.ctrls.val = []) (hpos : st.pos.val = data.length) :
    ∃ ops, BodyTokens tokens ops ∧ FunctionTyped ctx bt ops := by
  cases h with
  | running parents current remaining _ hopen _ _ _ =>
      obtain ⟨_, _, _, _, _, _, hc, _⟩ := hopen
      simp [hctrls] at hc
  | closed ops done remaining _ _ hbody htyped hrest htrace =>
      have hempty := hrest.empty_iff.mpr hpos
      subst remaining
      exact ⟨ops, by simpa [htrace] using hbody, htyped⟩

/-- All information available while dispatching one opcode. The runtime cursor
has consumed the opcode, and the token relation fixes its remaining immediate. -/
structure Pending (data : Slice U8) (tokens : List Token) (ctx : code.Context)
    (bt : code.BlockType) (st : code.OpIterState) (token : Token) where
  start : Usize
  next : Usize
  parents : List Frames.Saved
  current : Frames.Saved
  remaining : List Token
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  opened : Frames.Open (functionContext ctx) st parents current
  bodyType : Frames.bodyType parents current = some bt
  encoded : At data start token next
  rest : Rest data next remaining
  trace : tokens = Frames.trace parents current ++ token :: remaining
  pos : st.pos.val = start.val + 1
  vals : st.vals.val.length ≤ start.val
  ctrls : st.ctrls.val.length ≤ start.val + 1

theorem Pending.val_capacity {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) : st.vals.val.length + 1 < Usize.max := by
  have := p.encoded.span
  have := p.size
  have := p.vals
  have := Body.byte_limit_room
  omega

theorem Pending.ctrl_capacity {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) : st.ctrls.val.length < Usize.max := by
  have := p.encoded.span
  have := p.size
  have := p.ctrls
  have := Body.byte_limit_room
  omega

theorem Pending.next_ge {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) : st.pos.val ≤ p.next.val := by
  have := p.encoded.span
  have := p.pos
  omega

theorem Pending.bounds_after {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) (st' : code.OpIterState)
    (hpos : st'.pos = p.next)
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1)
    (hctrls : st'.ctrls.val.length ≤ st.ctrls.val.length + 1) : Bounds data st' := by
  have := p.encoded.span
  have := p.vals
  have := p.ctrls
  constructor
  · exact p.size
  · simpa [hpos] using p.encoded.span.2
  · rw [hpos]; omega
  · rw [hpos]; omega

theorem Pending.running_after {data tokens ctx bt st token}
    (p : Pending data tokens ctx bt st token) (st' : code.OpIterState)
    (parents : List Frames.Saved) (current : Frames.Saved)
    (hopen : Frames.Open (functionContext ctx) st' parents current)
    (hbody : Frames.bodyType parents current = some bt)
    (htrace : Frames.trace parents current = Frames.trace p.parents p.current ++ [token])
    (hpos : st'.pos = p.next)
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1)
    (hctrls : st'.ctrls.val.length ≤ st.ctrls.val.length + 1) : State data tokens ctx bt st' := by
  apply State.running st' parents current p.remaining
    (p.bounds_after st' hpos hvals hctrls) hopen hbody
  · simpa [hpos] using p.rest
  · simpa [htrace, List.append_assoc] using p.trace

theorem Pending.closed_after {data tokens ctx bt st}
    (p : Pending data tokens ctx bt st .end_) (st' : code.OpIterState)
    (ops : List instr)
    (hctrls : st'.ctrls.val = [])
    (hbody : BodyTokens (Frames.trace p.parents p.current ++ [.end_]) ops)
    (htyped : FunctionTyped ctx bt ops)
    (hpos : st'.pos = p.next)
    (hvals : st'.vals.val.length ≤ st.vals.val.length + 1) : State data tokens ctx bt st' := by
  apply State.closed st' ops (Frames.trace p.parents p.current ++ [.end_]) p.remaining
    (p.bounds_after st' hpos hvals (by simp [hctrls])) hctrls hbody htyped
  · simpa [hpos] using p.rest
  · simpa [List.append_assoc] using p.trace

end Itasca.Core
