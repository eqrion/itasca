import Itasca.Wasm2.Control.Frame
import Itasca.Wasm2.TableAdapters
import Itasca.Wasm2.Control.FuncType
import Itasca.Handler.EnvReaders
import Itasca.Wasm2.ProfileFilters

/-!
# Totality of the control handlers

Termination and structural-invariant preservation for the extracted control handlers
`code.push_frame`, `code.branch`, `code.enter`, `code.branch_table`, `code.call` and their
metadata-returning helpers, on arbitrary bytes and environments. Each result keeps
`Control.Shape` and the alignment of the `blocks` vector with the control vector.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 1000000

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

/-- Erasing the active operand segment preserves structural frame bounds,
including the empty-control-stack case. -/
@[step]
theorem code.mark_unreachable_total (st : code.OpIterState)
    (hs : Control.Shape st) :
    code.mark_unreachable st ⦃ s =>
      Control.Shape s ∧ s.ctrls.val.length = st.ctrls.val.length ∧ s.pos = st.pos ∧
      s.vals.val.length ≤ st.vals.val.length ∧
      s.ctrls.val.map code.Ctrl.signature = st.ctrls.val.map code.Ctrl.signature ⦄ := by
  rcases List.eq_nil_or_concat' st.ctrls.val with he | ⟨cs, c, he⟩
  · unfold code.mark_unreachable
    step with code.cur_base.spec st
    subst base
    step with code.mark_unreachable_loop.spec st (Control.base st) hs.base_le
    step*
    simp_all
    all_goals simp_all [Control.base]
    exact ⟨by simp [he], by simp [he]⟩
  · obtain ⟨s, hr, hv, hl, hc, hp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st cs c he (hs.bounded c (by simp [he])))
    rw [hr, WP.spec_ok]
    exact ⟨hs.unreachable cs c he hc hl, by simp [hc, he], hp,
      by simp [hv], by simp [hc, he]⟩

/-- `code.push_frame` is total and adds one aligned frame at the current stack height. -/
@[step]
theorem code.push_frame.total (st : code.BodyState)
    (kind : code.LabelKind) (bt : signature.BlockType)
    (hshape : Control.Shape st.core)
    (halign : st.blocks.val.length = st.core.ctrls.val.length)
    (hcap : st.blocks.val.length < Usize.max) :
    code.push_frame st kind bt ⦃ s =>
      Control.Shape s.core ∧ s.blocks.val.length = s.core.ctrls.val.length ∧
      s.core.pos = st.core.pos ∧ s.core.vals = st.core.vals ∧
      s.blocks.val.length = st.blocks.val.length + 1 ⦄ := by
  apply WP.spec_mono (code.push_frame.spec st kind bt (by omega))
  rintro s ⟨hc, hv, hp, hb⟩
  exact ⟨Wasm2.shape_push hshape kind bt hc hv, by simp [hb, hc], hp, hv, by simp [hb]⟩

/-- Branches preserve frame alignment and bounds for arbitrary label bytes and
arbitrary environments. Conditional branches restore the entire signature. -/
theorem code.branch.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch st data env conditional ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  rw [code.branch.eq_core]
  unfold Wasm2.branchCore
  step with code.read_multi_value_label.spec st data ha as ⟨r, st1, hv, hc, hblocks, hpos, hres⟩
  have hs' : Control.Shape st1.core :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  have ha' : st1.blocks.val.length = st1.core.ctrls.val.length := by simp_all
  cases conditional <;> step* <;> simp_all

/-- Reading and entering a block is total on arbitrary bytes. Popping block
parameters before fixing the frame's base preserves nested frame bounds. -/
theorem code.enter_info.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (kind : code.LabelKind)
    (hs : Control.Shape st.core) (hcap : st.blocks.val.length < Usize.max) :
    code.enter_info st data env profile kind ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length + 1 ∧
      st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.enter_info
  obtain ⟨res, hr, hdecoded⟩ := WP.spec_imp_exists (signature.read_block_type.spec data st.core.pos)
  rw [hr]
  cases res with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hs]
  | Ok pair =>
    obtain ⟨bt, next⟩ := pair
    have hpnext := hdecoded.span.1.le
    simp only [bind_ok]
    have hbranch : core.result.Result.Insts.CoreOpsTry.branch
        (.Ok (bt, next) : core.result.Result (signature.BlockType × Usize) error.OpError) =
        .ok (.Continue (bt, next)) := rfl
    rw [hbranch]
    simp only [bind_ok]
    have hspos : Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    simp only [signature.BlockType.params.spec]
    cases bt <;> cases kind <;> step* <;> simp_all

@[step]
theorem code.take_index.shape (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) :
    code.take_index st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ⦄ := by
  obtain ⟨⟨r, out⟩, hr, hv, hc, hd⟩ := WP.spec_imp_exists (code.take_index.spec st data)
  dsimp only at hv hc hd
  rw [hr, WP.spec_ok]
  refine ⟨?_, hc, ?_⟩
  · exact ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  · cases r with
    | Err e => simpa only [hd.2] using Nat.le_refl st.pos.val
    | Ok index => exact (Leb128.Decoded.span _ _ _ _ hd).1.le

@[step]
theorem types.ElemType.value_type.total (ty : types.ElemType) :
    types.ElemType.value_type ty ⦃ _ => True ⦄ := by
  cases ty <;> simp [types.ElemType.value_type]

@[step]
theorem types.ValueType.ne.total (a b : types.ValueType) :
    core.cmp.PartialEq.ne.trait_default types.ValueType.Insts.CoreCmpPartialEqValueType a b
      ⦃ _ => True ⦄ := by
  cases a <;> cases b <;>
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      types.ValueType.Insts.CoreCmpPartialEqValueType.eq]

@[step]
theorem code.call_info.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (hs : Control.Shape st.core) :
    code.call_info st data env ⦃ r =>
      Control.Shape r.2.core ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.call_info
  step* <;> simp_all

@[step]
theorem code.call_indirect_info.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (hs : Control.Shape st.core) :
    code.call_indirect_info st data env profile ⦃ r =>
      Control.Shape r.2.core ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧
        st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.call_indirect_info
  step* <;> simp_all <;> omega

end Itasca
