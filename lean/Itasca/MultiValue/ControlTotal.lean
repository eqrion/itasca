import Itasca.MultiValue.Control
import Itasca.MultiValue.TableAdapters
import Itasca.MultiValue.Calls

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
    step* <;> simp_all
    all_goals simp_all [Control.base]
    exact ⟨by simp [he], by simp [he]⟩
  · obtain ⟨s, hr, hv, hl, hc, hp⟩ := WP.spec_imp_exists
      (code.mark_unreachable.spec st cs c he (hs.bounded c (by simp [he])))
    rw [hr, WP.spec_ok]
    exact ⟨hs.unreachable cs c he hc hl, by simp [hc, he], hp,
      by simp [hv], by simp [hc, he]⟩

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
  apply WP.spec_mono (code.push_frame.spec st kind bt (by omega) hcap)
  rintro s ⟨hc, hv, hp, hb⟩
  exact ⟨MultiValue.shape_push hshape kind bt hc hv, by simp [hb, hc, halign], hp, hv, by simp [hb]⟩

/-- Branches preserve frame alignment and bounds for arbitrary label bytes and
arbitrary environments. Conditional branches restore the entire signature. -/
theorem code.branch.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch st data env conditional ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  rw [code.branch.eq_core]
  unfold MultiValue.branchCore
  step with code.read_multi_value_label.spec st data ha as ⟨r, st1, hv, hc, hblocks, hpos, hres⟩
  have hs' : Control.Shape st1.core :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  have ha' : st1.blocks.val.length = st1.core.ctrls.val.length := by simp_all
  cases conditional <;> step* <;> simp_all

/-- Reading and entering a block is total on arbitrary bytes. Popping block
parameters before fixing the new base preserves nested frame bounds. -/
theorem code.enter_info.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (kind : code.LabelKind) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hcap : st.blocks.val.length < Usize.max) :
    code.enter_info st data env kind ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length + 1 ∧
      st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.enter_info
  obtain ⟨res, hr, hdecoded⟩ := WP.spec_imp_exists (signature.read_block_type.spec data st.core.pos)
  rw [hr]
  cases res with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hs, ha]
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

/-- Erasing callback metadata preserves the complete entry-state contract. -/
theorem code.enter.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (kind : code.LabelKind) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hcap : st.blocks.val.length < Usize.max) :
    code.enter st data env kind ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length + 1 ∧
      st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  unfold code.enter
  step with code.enter_info.total st data env kind hs ha hcap
    as ⟨r, s, hshape, halign, hlen, hpos⟩
  cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The table loop includes its default target without incrementing the
possibly maximal encoded count. Every iteration checks the original suffix. -/
theorem code.branch_table_loop.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (count : U32) (arity : Option Usize) (i : U32)
    (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) (hi : i.val ≤ count.val) :
    code.branch_table_loop st.core st.blocks data env count arity i ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  have hlo : code.branch_table_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      st.core data env () count arity i ⦃ r =>
      Control.Shape r.2.1.core ∧ r.2.1.blocks.val.length = r.2.1.core.ctrls.val.length ∧
      r.2.1.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.1.core.pos.val ⦄ := by
    unfold code.branch_table_with_loop
    apply loop.spec_decr_nat (fun p => count.val - p.2.2.2.val)
      (fun p => Control.Shape p.1 ∧ (code.BodyState.mk p.1).blocks.val.length = p.1.ctrls.val.length ∧
        (code.BodyState.mk p.1).blocks = st.blocks ∧ p.2.2.2.val ≤ count.val ∧ st.core.pos.val ≤ p.1.pos.val)
    · rintro ⟨stateCore, visitor, arity, j⟩ ⟨hs', ha', hb', hj, hpos⟩
      cases visitor
      dsimp only at hs' ha' hb' hj hpos
      dsimp only
      rw [MultiValue.tableBody_eq data env count stateCore (code.BodyState.mk stateCore).blocks arity j]
      apply ResultFacts.map_spec
      unfold code.branch_table_loop.body
      obtain ⟨⟨r, s⟩, hr, hv, hc, hb, hp, hread⟩ := WP.spec_imp_exists
        (code.read_multi_value_label.spec ⟨stateCore⟩ data ha')
      rw [hr]
      simp only [bind_ok]
      dsimp only at hv hc hb hp hread
      have hss : Control.Shape s.core :=
        ⟨by simpa [hc] using hs'.ordered, by simpa [hc, hv] using hs'.bounded⟩
      have has : s.blocks.val.length = s.core.ctrls.val.length := by simp_all
      have hbs : s.blocks = st.blocks := by simp_all
      have hprogress : st.core.pos.val ≤ s.core.pos.val := by omega
      cases arity <;> step* by simp_all [MultiValue.tableFlow, MultiValue.tableCont, MultiValue.tableDone]
      all_goals simp_all [MultiValue.tableFlow, MultiValue.tableCont, MultiValue.tableDone]
      all_goals scalar_tac
    · exact ⟨hs, ha, rfl, hi, le_refl _⟩
  unfold code.branch_table_loop
  obtain ⟨⟨res, final, visitor⟩, hr, hp⟩ := WP.spec_imp_exists hlo
  simpa [hr] using hp

@[step]
theorem code.branch_table.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_table st data env ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  rw [code.branch_table.eq_core]
  unfold MultiValue.tableCore
  step with reader.read_u32_leb.spec data st.core.pos as ⟨res, hdecoded⟩
  step
  split
  · rename_i _ pair
    obtain ⟨count, next⟩ := pair
    have hpnext : st.core.pos.val ≤ next.val := by
      cases res <;> simp_all [Leb128.Post]
      cases cf_post
      exact (Leb128.Decoded.span _ _ _ _ hdecoded).1.le
    have hspos : Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    step with code.pop_with_type.total _ .I32 hspos as ⟨r, s, hs', hc, hp, hv, he⟩
    step
    split
    · apply WP.spec_mono (code.branch_table_loop.total ⟨s⟩ data env count none
        0#u32 hs' (by simp_all) (by simp))
      intro result hout
      exact ⟨hout.1, hout.2.1, by simpa [hc] using hout.2.2.1, hpnext.trans (by simpa [hp] using hout.2.2.2)⟩
    · step* <;> simp_all
  · step* <;> simp_all

@[step]
theorem code.call.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (indirect : Bool) (hs : Control.Shape st.core) :
    code.call st data env indirect ⦃ r =>
      Control.Shape r.2.core ∧ r.2.core.ctrls = st.core.ctrls ∧ r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  rw [code.call.eq_core]
  unfold MultiValue.callCore
  step with reader.read_u32_leb.spec data st.core.pos as ⟨res, hdecoded⟩
  step
  split
  · rename_i _ pair
    obtain ⟨index, next⟩ := pair
    have hpnext : st.core.pos.val ≤ next.val := by
      cases res <;> simp_all [Leb128.Post]
      cases cf_post
      exact (Leb128.Decoded.span _ _ _ _ hdecoded).1.le
    have hspos : Control.Shape { st.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
    step
    cases indirect
    · step* <;> simp_all
    · simp only [↓reduceIte]
      by_cases hn : next.val < data.length
      · step with reader.read_byte.spec data next hn as ⟨r1, next1, hbyte, hnext⟩
        subst r1
        step as ⟨cf1, hcf1⟩
        subst cf1
        have hsnext (p : Usize) : Control.Shape { st.core with pos := p } :=
          ⟨hs.ordered, hs.bounded⟩
        simp only [alloc.vec.Vec.is_empty, bind_ok]
        step* <;> simp_all <;> omega
      · rw [reader.read_byte.eof data next (by omega)]
        step* <;> simp_all
  · step* <;> simp_all

end Itasca
