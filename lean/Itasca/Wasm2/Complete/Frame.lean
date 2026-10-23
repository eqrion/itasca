import Itasca.Binary.Wasm2.EncodingComplete
import Itasca.Wasm2.Invariant
import Itasca.Wasm1.Complete.Frame
import Itasca.Profile.Types

/-!
# Frames for Wasm 2.0 completeness

Defines `Completeness.Frame`, a Wasm 2.0 body state with an explicit control frame and block
descriptor stack, together with its output relation `Frame.Output`. `Completeness.Bounds` records
the size invariants that keep operand and control counts below `Usize.max`. `Labels` relates the
runtime block descriptors to the SpecTec label context.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- The SpecTec result type of the label at `depth`, with innermost labels first, if any. -/
def labelTypes (env : module.Env) (st : code.BodyState) (depth : Nat) : Option resulttype :=
  ((labelAt st depth).bind (resolve env)).map (fun ts => .mk_list (ts.map Translate.valueType))

/-- Exact correspondence between the physical descriptors and declarative
label types, with innermost labels first. -/
def Labels (env : module.Env) (st : code.BodyState) (C : context) : Prop :=
  ∀ depth, C.LABELS[depth]? = labelTypes env st depth

theorem labelAt_congr {st s : code.BodyState}
    (hb : s.blocks.val = st.blocks.val)
    (hc : s.core.ctrls.val.map code.Ctrl.kind = st.core.ctrls.val.map code.Ctrl.kind)
    (depth : Nat) : labelAt s depth = labelAt st depth := by
  unfold labelAt
  rw [hb]
  simp only [code.BodyState.blocks_length]
  split
  · have he := congrArg (fun cs => cs[st.core.ctrls.val.length - 1 - depth]?) hc
    simp only [List.getElem?_map] at he
    cases hs : s.core.ctrls.val[st.core.ctrls.val.length - 1 - depth]? <;>
      cases ht : st.core.ctrls.val[st.core.ctrls.val.length - 1 - depth]? <;>
      simp only [hs, ht, Option.map_none, Option.map_some, Option.some.injEq] at he
    · simp [ht]
    · contradiction
    · contradiction
    · simp [ht, he]
  · rfl

namespace Completeness

/-- A Wasm 2.0 body state viewed as a Wasm 1.0 control frame plus its stack of block
descriptors. -/
structure Frame (st : code.BodyState) where
  core : Itasca.Wasm1.Completeness.Frame st.core
  parents : List signature.BlockType
  current : signature.BlockType
  blocks : st.blocks.val = parents ++ [current]
  aligned : parents.length = core.parents.length

theorem Frame.nonempty {st} (f : Frame st) : st.blocks.val ≠ [] := by simp [f.blocks]

/-- The state `s` realizes the operand stack `out` in the control frame of `st` and keeps its
block descriptors. -/
def Frame.Output {st} (f : Frame st) (out : List valtype) (s : code.BodyState) : Prop :=
  f.core.Output out s.core ∧ s.blocks = st.blocks

theorem Frame.output_self {st} (f : Frame st) {out : List valtype}
    (h : Sequence.Realizes f.core.current.polymorphic_base f.core.operands out) :
    f.Output out st := ⟨f.core.output_self h, rfl⟩

theorem Frame.Output.next {st s out} {f : Frame st} (h : f.Output out s) :
    ∃ g : Frame s, g.parents = f.parents ∧ g.current = f.current ∧
      g.core.parents = f.core.parents ∧ g.core.outer = f.core.outer ∧
      g.core.current.kind = f.core.current.kind ∧
      g.core.current.value_stack_base = f.core.current.value_stack_base ∧
      Sequence.Realizes g.core.current.polymorphic_base g.core.operands out := by
  obtain ⟨g, hp, ho, hk, hsig, hbase, hr⟩ := h.1.next
  exact ⟨⟨g, f.parents, f.current, by rw [h.2]; exact f.blocks,
    by rw [hp]; exact f.aligned⟩, rfl, rfl, hp, ho, hk, hbase, hr⟩

theorem Frame.Output.labels {env C st s out} {f : Frame st} (h : f.Output out s)
    (hl : Labels env st C) : Labels env s C := by
  intro depth
  rw [hl depth]
  unfold labelTypes
  rw [labelAt_congr (congrArg alloc.vec.Vec.val h.2) ?_ depth]
  obtain ⟨poly, operands, hc, hv, ht⟩ := h.1
  simp [hc, f.core.ctrls]

theorem Frame.Output.transfer {st s t out} {f : Frame st} {g : Frame s}
    (h : g.Output out t) (hs : s.blocks = st.blocks)
    (hp : g.core.parents = f.core.parents) (ho : g.core.outer = f.core.outer)
    (hk : g.core.current.kind = f.core.current.kind)
    (hbase : g.core.current.value_stack_base = f.core.current.value_stack_base) :
    f.Output out t := by
  have hsignatures : s.core.ctrls.val.map code.Ctrl.signature =
      st.core.ctrls.val.map code.Ctrl.signature := by
    simpa only [code.BodyState.blocks_val] using congrArg alloc.vec.Vec.val hs
  rw [g.core.ctrls, f.core.ctrls] at hsignatures
  have hsig : g.core.current.signature = f.core.current.signature := by
    have hl := congrArg List.getLast? hsignatures
    simpa using hl
  exact ⟨h.1.transfer hp ho hk hsig hbase, h.2.trans hs⟩

/-- Size invariants of a body prefix: the function is within `MAX_FUNCTION_BYTES`, and operand
and control counts grow at most linearly in the cursor. Each byte adds at most 500 values, and
the resulting bound fits even a 32-bit `usize`. -/
structure Bounds (data : Slice U8) (st : code.BodyState) : Prop where
  size : data.length ≤ limits.MAX_FUNCTION_BYTES.val
  pos : st.core.pos.val ≤ data.length
  vals : st.core.vals.val.length ≤ 500 * st.core.pos.val
  ctrls : st.blocks.val.length ≤ st.core.pos.val + 1

theorem capacity_margin : 500 * limits.MAX_FUNCTION_BYTES.val + 1001 < Usize.max := by
  simp only [limits.MAX_FUNCTION_BYTES]
  scalar_tac

theorem Bounds.val_capacity {data st} (h : Bounds data st) :
    st.core.vals.val.length + 1000 < Usize.max := by
  have := h.vals
  have := h.pos
  have := h.size
  have := capacity_margin
  omega

theorem Bounds.ctrl_capacity {data st} (h : Bounds data st) :
    st.blocks.val.length < Usize.max := by
  have := h.ctrls
  have := h.pos
  have := h.size
  have := limits.MAX_FUNCTION_BYTES.room
  omega

theorem bounds_after {data st s token next} (h : Bounds data st)
    (hat : At data st.core.pos token next) (hp : s.core.pos = next)
    (hv : s.core.vals.val.length ≤ st.core.vals.val.length + 500 * (next.val - st.core.pos.val))
    (hc : s.blocks.val.length ≤ st.blocks.val.length + 1) : Bounds data s := by
  have hs := hat.span
  have := h.vals
  have := h.ctrls
  refine ⟨h.size, by simpa [hp] using hs.2, ?_, ?_⟩ <;> rw [hp] <;> omega

end Completeness
end Itasca.Wasm2
