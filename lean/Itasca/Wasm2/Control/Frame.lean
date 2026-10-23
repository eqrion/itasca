import Itasca.Wasm2.SignatureEquality
import Itasca.Wasm2.HandlerAdapters
import Itasca.Binary.Wasm2.BlockType
import Itasca.Wasm2.Suffix

/-!
# Control frames and labels

The structural invariant of the extracted control stack and its label lookup. `Wasm2.Shape` says
that frame bases are ordered and within the operand stack and that the `blocks` vector is aligned
with the control vector. `code.push_frame.spec`, `code.label.spec` and
`code.read_multi_value_label.spec` describe frame creation and label decoding, with `Wasm2.labelAt`
as the specification of a branch depth.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

/-- Frame bases remain ordered and within the operand stack. The signature
projection has the same indexing as the runtime control vector. -/
structure Shape (st : code.BodyState) : Prop where
  core : Control.Shape st.core
  aligned : st.blocks.val.length = st.core.ctrls.val.length

/-- The control entry that `code.push_frame` creates, with its base at the current stack height. -/
def frame (st : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) : code.Ctrl :=
  ⟨kind, bt, alloc.vec.Vec.len st.vals, false⟩

/-- Pushing a frame at the current stack height preserves `Control.Shape`. -/
theorem shape_push {st st' : code.OpIterState} (h : Control.Shape st)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hctrls : st'.ctrls.val = st.ctrls.val ++ [frame st kind bt])
    (hvals : st'.vals = st.vals) : Control.Shape st' := by
  constructor
  · rw [hctrls, List.pairwise_append]
    exact ⟨h.ordered, by simp, by simpa [frame] using h.bounded⟩
  · intro c hc
    rw [hctrls] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simpa [hvals] using h.bounded c hc
    · have heq : c = frame st kind bt := by simpa using hc
      simp [heq, frame, hvals]

/-- The descriptor a branch to a frame carries: the parameters for `loop`, the results
otherwise. -/
def target (kind : code.LabelKind) (bt : signature.BlockType) : signature.ResultType :=
  match kind with
  | .Loop => inputs bt
  | _ => outputs bt

/-- The label descriptor at a branch depth, counted from the innermost frame. -/
def labelAt (st : code.BodyState) (depth : Nat) : Option signature.ResultType := do
  if depth < st.blocks.val.length then
    let i := st.blocks.val.length - 1 - depth
    let c ← st.core.ctrls.val[i]?
    let bt ← st.blocks.val[i]?
    some (target c.kind bt)
  else none

end Itasca.Wasm2

namespace Itasca

@[step]
theorem code.push_frame.spec (st : code.BodyState)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hc : st.core.ctrls.val.length < Usize.max) :
    code.push_frame st kind bt ⦃ s =>
      s.core.ctrls.val = st.core.ctrls.val ++ [Wasm2.frame st.core kind bt] ∧
      s.core.vals = st.core.vals ∧ s.core.pos = st.core.pos ∧
      s.blocks.val = st.blocks.val ++ [bt] ⦄ := by
  unfold code.push_frame
  step*
  simp_all [Wasm2.frame]

/-- Label lookup uses loop inputs and all other frames' outputs, in reverse
nesting order. Out-of-range labels produce an ordinary validation error. -/
@[step]
theorem code.label.spec (st : code.BodyState) (depth : U32)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.label st depth ⦃ r =>
      match r with
      | .Ok view => Wasm2.labelAt st depth.val = some view
      | .Err e => e = .UnknownLabel ∧ st.blocks.val.length ≤ depth.val ⦄ := by
  unfold code.label
  step
  split
  · simp only [WP.spec_ok]
    constructor
    · trivial
    · scalar_tac
  · step
    step
    step
    split <;> simp only [signature.BlockType.params.spec, signature.BlockType.results.spec, bind_ok, WP.spec_ok]
    all_goals simp_all [Wasm2.labelAt, Wasm2.target]
    all_goals have hi : depth.val < st.core.ctrls.val.length := by scalar_tac
    all_goals have hc : st.core.ctrls.val.length - 1 - depth.val < st.core.ctrls.val.length := by omega
    all_goals simp_all

theorem code.label.complete (st : code.BodyState) (depth : U32)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) (view : signature.ResultType)
    (hl : Wasm2.labelAt st depth.val = some view) :
    code.label st depth = .ok (.Ok view) := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (code.label.spec st depth ha)
  cases r with
  | Err e =>
    have hd : st.core.ctrls.val.length ≤ depth.val := by simpa using hs.2
    simp [Wasm2.labelAt, Nat.not_lt.mpr hd] at hl
  | Ok actual =>
    have he : actual = view := by simpa [hs] using hl
    simpa [he] using hr

/-- `code.read_label_info` decodes a LEB128 depth and resolves it with `Wasm2.labelAt`, leaving
the stack and frames unchanged. -/
@[step]
theorem code.read_label_info.spec (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      st.core.pos.val ≤ r.2.core.pos.val ∧
      (∀ depth view, r.1 = .Ok (depth, view) →
        Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        Wasm2.labelAt st depth.val = some view) ⦄ := by
  obtain ⟨r, hr, hs⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases r with
  | Err e => simp [code.read_label_info, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨depth, next⟩ := pair
    have hpnext : st.core.pos.val ≤ next.val := (Leb128.Decoded.span _ _ _ _ hs).1.le
    obtain ⟨r, hl, hp⟩ := WP.spec_imp_exists
      (code.label.spec { st with core := { st.core with pos := next } } depth ha)
    cases r with
    | Err e => simp [code.read_label_info, hr, hl, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hpnext]
    | Ok view =>
      simp [code.read_label_info, hr, hl, core.result.Result.Insts.CoreOpsTry.branch]
      exact ⟨hpnext, hs, hp⟩

/-- `code.read_multi_value_label` is `code.read_label_info` without the depth. -/
@[step]
theorem code.read_multi_value_label.spec (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_multi_value_label st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
      st.core.pos.val ≤ r.2.core.pos.val ∧
      (∀ view, r.1 = .Ok view → ∃ depth,
        Leb128.Decoded data st.core.pos depth r.2.core.pos ∧
        Wasm2.labelAt st depth.val = some view) ⦄ := by
  obtain ⟨⟨r, s⟩, hr, hv, hc, hb, hp, hl⟩ :=
    WP.spec_imp_exists (code.read_label_info.spec st data ha)
  dsimp only at hv hc hb hp hl
  cases r with
  | Err e =>
    simp [code.read_multi_value_label, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    simp_all
  | Ok pair =>
    obtain ⟨depth, view⟩ := pair
    simp [code.read_multi_value_label, hr, core.result.Result.Insts.CoreOpsTry.branch]
    simp_all
    exact ⟨depth, hl⟩

end Itasca
