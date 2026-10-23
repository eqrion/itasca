import Itasca.Wasm2.EmptyVisitorLoop
import Itasca.Wasm2.Control.EndTotal
import Itasca.Wasm2.Step.Total
import Itasca.Visitor.Accepts

/-!
# Totality of visiting body validation

Shows that `code.validate_body_with` terminates for every input and profile when the visitor's
callbacks return (`FullVisitor.Total`), without byte validity or environment hypotheses
(`code.validate_body_with.total`). The supporting lemmas cover the body loop
(`code.body_loop_loop.total`), its initial state, branch tables and branch information; each
iteration preserves `Control.Shape` and advances the cursor.
-/

open Aeneas Aeneas.Std

namespace Itasca

@[step] theorem code.branch_info.total (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (conditional : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_info st data env conditional ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ :=
  by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.branch.total st data env conditional hs ha)
  unfold code.branch at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  all_goals subst r; exact hp

@[step] theorem code.end_frame_info.total (st : code.BodyState) (env : module.Env)
    (isElse : Bool) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.end_frame_info st env isElse ⦃ r =>
      Control.Shape r.2.core ∧ r.2.blocks.val.length = r.2.core.ctrls.val.length ∧
      r.2.blocks.val.length ≤ st.blocks.val.length ∧ r.2.core.pos = st.core.pos ⦄ :=
  by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.end_frame.total st env isElse hs ha)
  unfold code.end_frame at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result <;>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
  all_goals subst r; exact hp

@[step] theorem code.read_label_info.total (st : code.BodyState) (data : Slice U8)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.read_label_info st data ⦃ r =>
      r.2.core.vals = st.core.vals ∧ r.2.core.ctrls = st.core.ctrls ∧
      r.2.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.core.pos.val ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (code.read_multi_value_label.spec st data ha)
  unfold code.read_multi_value_label at hr
  obtain ⟨⟨result, out⟩, hs, hnext⟩ := ResultFacts.bind_ok_inv _ _ _ hr
  rw [hs, WP.spec_ok]
  cases result with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hnext
    subst r
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp [core.result.Result.Insts.CoreOpsTry.branch] at hnext
    subst r
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

attribute [local step] code.pop_with_type.total code.check_suffix.spec

@[local step] private theorem label_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) :
    visitor.on_br_table_label v st depth ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_table_label v st depth
  simp [h]

@[local step] private theorem table_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32)
    (ts : signature.ResultType) :
    visitor.on_br_table v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_table v st depth ts
  simp [h]

@[local step] private theorem visit_total (r : core.result.Result Unit error.VisitError) :
    code.visit r ⦃ _ => True ⦄ := by
  cases r <;> simp [code.visit]

/-- Returning hooks preserve the structural branch-table invariant, including
rejections and the default target at the maximal encoded count. -/
theorem code.branch_table_with_loop.total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (v : V) (count : U32) (arity : Option Usize)
    (first : signature.ResultType) (i : U32)
    (hs : Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hi : i.val ≤ count.val) :
    code.branch_table_with_loop visitor st.core data env profile v count arity first i ⦃ r =>
      Control.Shape r.2.1.core ∧ r.2.1.blocks.val.length = r.2.1.core.ctrls.val.length ∧
      r.2.1.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.1.core.pos.val ⦄ := by
  unfold code.branch_table_with_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.2.2.2.val)
    (fun p => Control.Shape p.1 ∧ (code.BodyState.mk p.1).blocks.val.length = p.1.ctrls.val.length ∧
      (code.BodyState.mk p.1).blocks = st.blocks ∧ p.2.2.2.2.val ≤ count.val ∧
      st.core.pos.val ≤ p.1.pos.val)
  · rintro ⟨stateCore, v, arity, first, j⟩ ⟨hs', ha', hb', hj, hpos⟩
    dsimp only at hs' ha' hb' hj hpos
    dsimp only
    unfold code.branch_table_with_loop.body
    obtain ⟨⟨r, s⟩, hr, hvals, hc, hb, hp⟩ := WP.spec_imp_exists
      (code.read_label_info.total ⟨stateCore⟩ data ha')
    rw [hr]
    simp only [bind_ok]
    dsimp only at hvals hc hb hp
    have hss : Control.Shape s.core :=
      ⟨by simpa [hc] using hs'.ordered, by simpa [hc, hvals] using hs'.bounded⟩
    have has : s.blocks.val.length = s.core.ctrls.val.length := by simp_all
    have hbs : s.blocks = st.blocks := by simp_all
    have hprogress : st.core.pos.val ≤ s.core.pos.val := by omega
    cases r with
    | Err e => simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨depth, ts⟩ := pair
      have hbranch : core.result.Result.Insts.CoreOpsTry.branch
          (.Ok (depth, ts) : core.result.Result (U32 × signature.ResultType) error.OpError) =
          .ok (.Continue (depth, ts)) := rfl
      simp only [Std.uncurry, hbranch, bind_ok]
      have hfirst : (if j = 0#u32 then Result.ok ts else Result.ok first) =
          Result.ok (if j = 0#u32 then ts else first) := by split <;> rfl
      rw [hfirst]
      simp only [bind_ok]
      cases arity <;> step* by simp_all
      all_goals scalar_tac
  · exact ⟨hs, ha, rfl, hi, le_refl _⟩

@[step]
theorem code.branch_table_with.total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (v : V) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length) :
    code.branch_table_with visitor st data env profile v ⦃ r =>
      Control.Shape r.2.1.core ∧ r.2.1.blocks.val.length = r.2.1.core.ctrls.val.length ∧
      r.2.1.blocks = st.blocks ∧ st.core.pos.val ≤ r.2.1.core.pos.val ⦄ := by
  unfold code.branch_table_with
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
    step with code.pop_with_type.total _ .I32 hspos as ⟨r, s, hs', hc, hp, hvals, he⟩
    step
    split
    · apply WP.spec_mono (code.branch_table_with_loop.total visitor hv
        ⟨s⟩ data env profile v count none .Empty 0#u32 hs' (by simp_all) (by simp))
      intro result hout
      exact ⟨hout.1, hout.2.1, by simpa [hc] using hout.2.2.1, hpnext.trans (by simpa [hp] using hout.2.2.2)⟩
    · step*
      simp_all
  · step*

@[local step] private theorem block_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_block v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_block v st bt
  simp [h]

@[local step] private theorem loop_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_loop v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_loop v st bt
  simp [h]

@[local step] private theorem if_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_if v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_if v st bt
  simp [h]

@[local step] private theorem else_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (bt : signature.BlockType) :
    visitor.on_else v st bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_else v st bt
  simp [h]

@[local step] private theorem end_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) :
    visitor.on_end v st kind bt ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_end v st kind bt
  simp [h]

@[local step] private theorem br_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) (ts : signature.ResultType) :
    visitor.on_br v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br v st depth ts
  simp [h]

@[local step] private theorem br_if_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (depth : U32) (ts : signature.ResultType) :
    visitor.on_br_if v st depth ts ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_br_if v st depth ts
  simp [h]

@[local step] private theorem return_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState)  :
    visitor.on_return v st ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_return v st
  simp [h]

@[local step] private theorem call_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (index : U32) :
    visitor.on_call v st index ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_call v st index
  simp [h]

@[local step] private theorem call_indirect_hook_total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (v : V) (st : code.OpIterState) (index table : U32) :
    visitor.on_call_indirect v st index table ⦃ _ => True ⦄ := by
  obtain ⟨r, w, h⟩ := hv.on_call_indirect v st index table
  simp [h]

attribute [local step] code.enter_info.total

set_option maxHeartbeats 2000000 in
/-- Every returned body iteration preserves the structural invariant and every
continuing iteration advances the byte cursor. Returning hooks may reject. -/
theorem code.body_loop_loop.body.total {V : Type}
    (visitor : code.OpVisitor V) (hv : FullVisitor.Total visitor)
    (data : Slice U8) (env : module.Env) (ctx : code.Context) (type_index : U32)
    (profile : ValidationProfile) (s : code.BodyState) (v : V)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape s.core)
    (ha : s.blocks.val.length = s.core.ctrls.val.length)
    (hb : s.blocks.val.length ≤ s.core.pos.val + 1) :
    code.body_loop_loop.body visitor data env ctx type_index profile v s ⦃ r =>
      match r with
      | .done _ => True
      | .cont p => (Control.Shape p.2.core ∧
          p.2.blocks.val.length = p.2.core.ctrls.val.length ∧
          p.2.blocks.val.length ≤ p.2.core.pos.val + 1) ∧
          Usize.max - p.2.core.pos.val < Usize.max - s.core.pos.val ⦄ := by
  unfold code.body_loop_loop.body code.step_profile
  simp only [alloc.vec.Vec.is_empty, bind_ok]
  split
  · split <;> simp
  · by_cases hp : s.core.pos.val < data.length
    · obtain ⟨res, hr, next, hres, hn⟩ := WP.spec_imp_exists
        (reader.read_byte.spec data s.core.pos hp)
      rw [hres] at hr
      rw [hr]
      simp only [bind_ok]
      have hbranch : core.result.Result.Insts.CoreOpsTry.branch
          (.Ok (data.val[s.core.pos.val], next) : core.result.Result (U8 × Usize) error.OpError) =
          .ok (.Continue (data.val[s.core.pos.val], next)) := rfl
      rw [hbranch]
      simp only [bind_ok, Std.uncurry]
      have hspos : Control.Shape { s.core with pos := next } := ⟨hs.ordered, hs.bounded⟩
      have hcap : s.blocks.val.length < Usize.max := by
        have := limits.MAX_FUNCTION_BYTES.room
        omega
      have hpos : s.core.pos.val < Usize.max := by
        have := limits.MAX_FUNCTION_BYTES.room
        omega
      obtain ⟨rc, hrc, _⟩ := WP.spec_imp_exists (code.check_opcode.spec profile data.val[s.core.pos.val])
      rw [hrc]
      cases rc with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
      cases u
      have hok : core.result.Result.Insts.CoreOpsTry.branch
          (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
      simp only [bind_ok]
      rw [hok]
      simp only [bind_ok]
      split
      all_goals try simp only [Std.bind_assoc, Std.uncurry]
      case h_12 =>
        rename_i _ h2 h3 h4 h5 h11 h12 h13 h14 h15 h16 h17
        have hscalar : (data.val[s.core.pos.val]).val ∉ Wasm2.controlOpcodes := by
          have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val :=
            fun he => h (UScalar.eq_of_val_eq he)
          simp only [Wasm2.controlOpcodes, List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨neq h2, neq h3, neq h4, neq h5, neq h11, neq h12,
            neq h13, neq h14, neq h15, neq h16, neq h17⟩
        split
        · simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        · have hsize : s.core.vals.val.length < Usize.max := by scalar_tac
          step with Wasm2.wasm2_total visitor
            { s.core with pos := next } data env ctx
            data.val[s.core.pos.val] v hspos hsize hscalar hv
            as ⟨r, hsc, hcount, hp'⟩
          rcases r with ⟨r, sc, v'⟩
          cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          scalar_tac
      all_goals step*
      all_goals try (cases x)
      all_goals try simp only [Std.bind_assoc, Std.uncurry]
      all_goals step*
      all_goals try (cases x)
      all_goals try simp only [Std.bind_assoc]
      all_goals step*
      all_goals simp_all
      all_goals try constructor
      all_goals scalar_tac
    · rw [reader.read_byte.eof data s.core.pos (by omega)]
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

set_option maxHeartbeats 2000000 in
/-- The actual visiting body loop terminates for structurally bounded states.
Every continuing iteration consumes an opcode; rejecting hooks terminate early. -/
theorem code.body_loop_loop.total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (type_index : U32) (profile : ValidationProfile) (st : code.BodyState)
    (v : V) (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hs : Control.Shape st.core)
    (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (hb : st.blocks.val.length ≤ st.core.pos.val + 1) :
    code.body_loop_loop visitor data env ctx type_index profile v st ⦃ _ => True ⦄ := by
  unfold code.body_loop_loop
  apply loop.spec_decr_nat (fun p => Usize.max - p.2.core.pos.val)
    (fun p => Control.Shape p.2.core ∧ p.2.blocks.val.length = p.2.core.ctrls.val.length ∧
      p.2.blocks.val.length ≤ p.2.core.pos.val + 1)
  · rintro ⟨v, s⟩ ⟨hs, ha, hb⟩
    dsimp only
    apply WP.spec_mono (code.body_loop_loop.body.total visitor hv data env ctx type_index profile
      s v hdata hs ha hb)
    intro r hr
    cases r <;> exact hr
  · exact ⟨hs, ha, hb⟩

attribute [local step] code.body_loop_loop.total

/-- Initialization is total and supplies the shared loop invariant. -/
@[step] theorem code.initial_state.total (env : module.Env) (index : U32) :
    code.initial_state env index ⦃ r =>
      match r with
      | .Err _ => True
      | .Ok st => Control.Shape st.core ∧
          st.blocks.val.length = st.core.ctrls.val.length ∧
          st.blocks.val.length ≤ st.core.pos.val + 1 ⦄ := by
  have hi : Control.Shape
      { vals := alloc.vec.Vec.new _, ctrls := alloc.vec.Vec.new _, pos := 0#usize } :=
    ⟨by simp, by simp⟩
  unfold code.initial_state
  step* <;> simp_all; scalar_tac

/-- Returning opcode hooks suffice for totality on arbitrary input in either profile; no byte
validity, signature, or environment hypothesis is required. -/
theorem code.validate_body_with.total {V : Type} (visitor : code.OpVisitor V)
    (hv : FullVisitor.Total visitor) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (type_index : U32) (profile : ValidationProfile) (v : V) :
    ∃ r, code.validate_body_with visitor data env ctx type_index profile v = .ok r := by
  have ht : code.validate_body_with visitor data env ctx type_index profile v ⦃ _ => True ⦄ := by
    unfold code.validate_body_with
    simp only [Slice.len]
    split
    · simp
    · have hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val := by scalar_tac
      step with code.initial_state.total env type_index as ⟨r, hr⟩
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok st =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, code.body_loop]
        exact code.body_loop_loop.total visitor hv data env ctx type_index profile st v
          hdata hr.1 hr.2.1 hr.2.2
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists ht
  exact ⟨r, hr⟩

end Itasca
