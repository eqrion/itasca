import Itasca.Wasm2.Visitor.Body

/-!
# Agreement of the two profiles

The Wasm 1.0 body reader is the Wasm 2.0 reader with filters that only reject. For the `br_table`
target loop, one reader step and the body loop, `wasm1` shows that a returned Wasm 1.0 run either
returns the same result under Wasm 2.0 or is a filter rejection, which the empty visitor also
reaches; `wasm1_returns` shows that the Wasm 1.0 run returns whenever the Wasm 2.0 run does.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca

theorem code.enter_info.wasm1 (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (kind : code.LabelKind) :
    code.enter_info st data env .Wasm1 kind = code.enter_info st data env .Wasm2 kind ∨
      ∃ e s, code.enter_info st data env .Wasm1 kind = .ok (.Err e, s) := by
  unfold code.enter_info
  obtain ⟨r, h, _⟩ := WP.spec_imp_exists (signature.read_block_type.spec data st.core.pos)
  rw [h]
  cases r with
    | Err e => left; simp [core.result.Result.Insts.CoreOpsTry.branch]
    | Ok pair =>
      obtain ⟨bt, next⟩ := pair
      obtain ⟨rc, hc, _⟩ := WP.spec_imp_exists (code.check_block_type.spec .Wasm1 bt)
      cases rc with
      | Err e =>
        right
        exact ⟨e, { st with core := { st.core with pos := next } }, by
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]⟩
      | Ok u =>
        left
        simp [hc, code.check_block_type.wasm2, core.result.Result.Insts.CoreOpsTry.branch]

theorem code.call_indirect_info.wasm1 (st : code.BodyState) (data : Slice U8) (env : metadata.Env) :
    code.call_indirect_info st data env .Wasm1 = code.call_indirect_info st data env .Wasm2 ∨
      ∃ e s, code.call_indirect_info st data env .Wasm1 = .ok (.Err e, s) := by
  unfold code.call_indirect_info
  obtain ⟨⟨r, ois⟩, h, _⟩ := WP.spec_imp_exists (code.take_index.spec st.core data)
  rw [h]
  cases r with
    | Err e => left; simp [core.result.Result.Insts.CoreOpsTry.branch]
    | Ok index =>
      obtain ⟨rc, hc, _⟩ := WP.spec_imp_exists (code.check_table_byte.spec .Wasm1 data ois.pos)
      cases rc with
      | Err e =>
        right
        exact ⟨e, { core := ois }, by
          simp [hc, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]⟩
      | Ok u =>
        left
        simp [hc, code.check_table_byte.wasm2, core.result.Result.Insts.CoreOpsTry.branch]

private theorem tableLoop_unfold {V : Type} (visitor : code.OpVisitor V) (ois : code.OpIterState)
    (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile) (w : V) (count : U32)
    (arity : Option Usize) (first : signature.ResultType) (i : U32) :
    code.branch_table_with_loop visitor ois data env profile w count arity first i =
      (do
        let cf ← Wasm2.Visitor.tableBody visitor data env profile count ⟨ois⟩ w arity first i
        match cf with
        | .cont (o, u, a, f, j) => code.branch_table_with_loop visitor o data env profile u count a f j
        | .done res => .ok res) := by
  conv_lhs => unfold code.branch_table_with_loop; rw [loop]
  rw [← Wasm2.Visitor.tableBody_eq]
  congr 1
  funext cf
  cases cf <;> rfl

/-- After a passing target check, the Wasm 1.0 table iteration is the Wasm 2.0 iteration. -/
private theorem tableBody_wasm1 {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (count : U32) (st : code.BodyState) (w : V) (arity : Option Usize)
    (first : signature.ResultType) (i : U32) (cf)
    (h : Wasm2.Visitor.tableBody visitor data env .Wasm1 count st w arity first i = .ok cf) :
    Wasm2.Visitor.tableBody visitor data env .Wasm2 count st w arity first i = .ok cf ∨
      ∃ e s, cf = .done (.Err e, s, w) ∧ ∀ (W : Type) (other : code.OpVisitor W) (u : W),
        Wasm2.Visitor.tableBody other data env .Wasm1 count st u arity first i =
          .ok (.done (.Err e, s, u)) := by
  unfold Wasm2.Visitor.tableBody at h ⊢
  obtain ⟨⟨rd, s⟩, hrd, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hrd]
  cases rd with
  | Err e =>
    left
    simpa using h
  | Ok pair =>
    obtain ⟨depth, ts⟩ := pair
    simp only [bind_ok, Std.uncurry] at h ⊢
    obtain ⟨c, hc, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases c with
    | Err e =>
      right
      simp only [ok.injEq] at h
      refine ⟨e, s, h.symm, fun W other u => ?_⟩
      simp [hrd, hc]
    | Ok u =>
      left
      simpa [code.check_table_target.wasm2] using h

theorem code.branch_table_with_loop.wasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (count : U32) :
    ∀ (n : Nat) (ois : code.OpIterState) (arity : Option Usize) (first : signature.ResultType)
      (i : U32) (w : V) r, count.val - i.val = n → i.val ≤ count.val →
    code.branch_table_with_loop visitor ois data env .Wasm1 w count arity first i = .ok r →
    code.branch_table_with_loop visitor ois data env .Wasm2 w count arity first i = .ok r ∨
      (r.1 ≠ .Ok () ∧ ∃ e s, code.branch_table_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        ois data env .Wasm1 () count arity first i = .ok (.Err e, s, ())) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro ois arity first i w r hn hi h
  rw [tableLoop_unfold] at h
  obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rcases tableBody_wasm1 visitor data env count ⟨ois⟩ w arity first i cf hb with hb2 | ⟨e, s, rfl, hall⟩
  · cases cf with
    | done res =>
      left
      rw [tableLoop_unfold, hb2]
      simpa using ht
    | cont x =>
      obtain ⟨o, u, a, f, j⟩ := x
      have hp := Wasm2.Visitor.tableBody.cont_progress visitor data env .Wasm1 count ⟨ois⟩ w arity
        first i o u a f j hi hb
      rcases ih (count.val - j.val) (by omega) o a f j u r rfl hp.2 ht with h2 | ⟨hne, e, s, he⟩
      · left
        rw [tableLoop_unfold, hb2]
        simpa using h2
      · right
        refine ⟨hne, e, s, ?_⟩
        obtain ⟨cf', hw, ho⟩ := Wasm2.Visitor.tableBody.transfer visitor
          code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env .Wasm1
          count ⟨ois⟩ w () arity first i _ hb trivial
        cases cf' with
        | done p => simp [Wasm2.Visitor.tableObserve] at ho
        | cont p =>
          obtain ⟨o', u', a', f', j'⟩ := p
          cases u'
          simp only [Wasm2.Visitor.tableObserve, ControlFlow.cont.injEq, Prod.mk.injEq] at ho
          obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
          rw [tableLoop_unfold, hw]
          simpa using he
  · simp only [ok.injEq] at ht
    subst r
    right
    refine ⟨by simp, e, s, ?_⟩
    rw [tableLoop_unfold, hall]
    simp

theorem code.branch_table_with_loop.wasm1_returns {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (count : U32) :
    ∀ (n : Nat) (ois : code.OpIterState) (arity : Option Usize) (first : signature.ResultType)
      (i : U32) (w : V) r, count.val - i.val = n → i.val ≤ count.val →
    code.branch_table_with_loop visitor ois data env .Wasm2 w count arity first i = .ok r →
    ∃ r', code.branch_table_with_loop visitor ois data env .Wasm1 w count arity first i = .ok r' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro ois arity first i w r hn hi h
  rw [tableLoop_unfold] at h
  obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  have hb1 : Wasm2.Visitor.tableBody visitor data env .Wasm1 count ⟨ois⟩ w arity first i = .ok cf ∨
      ∃ res, Wasm2.Visitor.tableBody visitor data env .Wasm1 count ⟨ois⟩ w arity first i =
        .ok (.done res) := by
    unfold Wasm2.Visitor.tableBody at hb ⊢
    obtain ⟨⟨rd, s⟩, hrd, hb⟩ := ResultFacts.bind_ok_inv _ _ _ hb
    rw [hrd]
    cases rd with
    | Err e => left; simpa using hb
    | Ok pair =>
      obtain ⟨depth, ts⟩ := pair
      simp only [bind_ok, Std.uncurry] at hb ⊢
      obtain ⟨c, hc, _⟩ := WP.spec_imp_exists (code.check_table_target.spec .Wasm1 env
        (if i = 0#u32 then ts else first) ts)
      cases c with
      | Err e => right; exact ⟨(.Err e, s, w), by simp [hc]⟩
      | Ok u => left; simpa [hc, code.check_table_target.wasm2] using hb
  rcases hb1 with hb1 | ⟨res, hres⟩
  · cases cf with
    | done res => exact ⟨res, by rw [tableLoop_unfold, hb1]; simp⟩
    | cont x =>
      obtain ⟨o, u, a, f, j⟩ := x
      have hp := Wasm2.Visitor.tableBody.cont_progress visitor data env .Wasm1 count ⟨ois⟩ w arity
        first i o u a f j hi hb1
      obtain ⟨r', hr'⟩ := ih (count.val - j.val) (by omega) o a f j u r rfl hp.2 ht
      exact ⟨r', by rw [tableLoop_unfold, hb1]; simpa using hr'⟩
  · exact ⟨res, by rw [tableLoop_unfold, hres]; simp⟩

theorem code.branch_table_with.wasm1 {V : Type} (visitor : code.OpVisitor V) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (w : V) r
    (h : code.branch_table_with visitor st data env .Wasm1 w = .ok r) :
    code.branch_table_with visitor st data env .Wasm2 w = .ok r ∨
      (r.1 ≠ .Ok () ∧ ∃ e s, code.branch_table_with code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        st data env .Wasm1 () = .ok (.Err e, s, ())) := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨rr, hrr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hrr]
  cases rr with
  | Err e =>
    left
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨rp, ois⟩, hrp, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hrp]
    cases rp with
    | Err e =>
      left
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
    | Ok u =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
      rcases code.branch_table_with_loop.wasm1 visitor data env count _ ois none .Empty 0#u32 w r
        rfl (by simp) h with h2 | ⟨hne, e, s, he⟩
      · exact .inl h2
      · exact .inr ⟨hne, e, s, by simpa [hrr, hrp, core.result.Result.Insts.CoreOpsTry.branch] using he⟩

theorem code.branch_table_with.wasm1_returns {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (w : V) r
    (h : code.branch_table_with visitor st data env .Wasm2 w = .ok r) :
    ∃ r', code.branch_table_with visitor st data env .Wasm1 w = .ok r' := by
  unfold code.branch_table_with at h ⊢
  obtain ⟨rr, hrr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rw [hrr]
  cases rr with
  | Err e => exact ⟨r, by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h⟩
  | Ok pair =>
    obtain ⟨count, next⟩ := pair
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
    obtain ⟨⟨rp, ois⟩, hrp, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hrp]
    cases rp with
    | Err e => exact ⟨r, by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h⟩
    | Ok u =>
      simp [core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
      obtain ⟨r', hr'⟩ := code.branch_table_with_loop.wasm1_returns visitor data env count _ ois
        none .Empty 0#u32 w r rfl (by simp) h
      exact ⟨r'.1, r'.2.1, r'.2.2, hr'⟩

private theorem step_br_table {V : Type} (visitor : code.OpVisitor V) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (profile : ValidationProfile) (w : V)
    (hc : code.check_opcode profile 14#u8 = .ok (.Ok ())) :
    code.step_profile visitor st data env ctx index profile 14#u8 w =
      code.branch_table_with visitor st data env profile w := by
  simp [code.step_profile, hc, global_simps, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  conv => rhs; rw [← Std.bind_pure (code.branch_table_with visitor st data env profile w)]
  congr 1
  funext x
  obtain ⟨r, s, u⟩ := x
  cases r <;> simp

/-- Outside `br_table`, a step that passes the opcode filter and whose entry or indirect-call
checks pass runs the same under both profiles. -/
private theorem step_profile.eq_of_infos {W : Type} (vis : code.OpVisitor W) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (op : U8) (u : W)
    (hc : code.check_opcode .Wasm1 op = .ok (.Ok ())) (htable : op ≠ 14#u8)
    (hblock : op = 2#u8 →
      code.enter_info st data env .Wasm1 .Block = code.enter_info st data env .Wasm2 .Block)
    (hloop : op = 3#u8 →
      code.enter_info st data env .Wasm1 .Loop = code.enter_info st data env .Wasm2 .Loop)
    (hif : op = 4#u8 →
      code.enter_info st data env .Wasm1 .Then = code.enter_info st data env .Wasm2 .Then)
    (hcall : op = 17#u8 →
      code.call_indirect_info st data env .Wasm1 = code.call_indirect_info st data env .Wasm2) :
    code.step_profile vis st data env ctx index .Wasm1 op u =
      code.step_profile vis st data env ctx index .Wasm2 op u := by
  unfold code.step_profile
  rw [hc, code.check_opcode.wasm2]
  split <;> first
    | exact absurd rfl htable
    | (rw [hblock rfl]) | (rw [hloop rfl]) | (rw [hif rfl]) | (rw [hcall rfl]) | rfl

/-- A step whose entry or indirect-call check fails rejects under Wasm 1.0 for every visitor. -/
private theorem step_profile.reject_of_info {W : Type} (vis : code.OpVisitor W)
    (st s : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (op : U8) (u : W) (e : error.OpError)
    (hc : code.check_opcode .Wasm1 op = .ok (.Ok ()))
    (hinfo : (op = 2#u8 ∧ code.enter_info st data env .Wasm1 .Block = .ok (.Err e, s)) ∨
      (op = 3#u8 ∧ code.enter_info st data env .Wasm1 .Loop = .ok (.Err e, s)) ∨
      (op = 4#u8 ∧ code.enter_info st data env .Wasm1 .Then = .ok (.Err e, s)) ∨
      (op = 17#u8 ∧ code.call_indirect_info st data env .Wasm1 = .ok (.Err e, s))) :
    code.step_profile vis st data env ctx index .Wasm1 op u = .ok (.Err e, s, u) := by
  rcases hinfo with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ <;>
    simp [code.step_profile, hc, he, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- One reader step either runs the same under both profiles for every visitor, rejects under
Wasm 1.0 for every visitor before any callback, or is a `br_table` that passed the opcode filter. -/
private theorem step_profile.cases (st : code.BodyState) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (op : U8) :
    (∀ (W : Type) (vis : code.OpVisitor W) (u : W),
      code.step_profile vis st data env ctx index .Wasm1 op u =
        code.step_profile vis st data env ctx index .Wasm2 op u) ∨
    (∃ e s, ∀ (W : Type) (vis : code.OpVisitor W) (u : W),
      code.step_profile vis st data env ctx index .Wasm1 op u = .ok (.Err e, s, u)) ∨
    (op = 14#u8 ∧ code.check_opcode .Wasm1 op = .ok (.Ok ())) := by
  obtain ⟨rc, hc, _⟩ := WP.spec_imp_exists (code.check_opcode.spec .Wasm1 op)
  cases rc with
  | Err e =>
    right; left
    exact ⟨e, st, fun W vis u => by
      simp [code.step_profile, hc, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]⟩
  | Ok u =>
    cases u
    by_cases h14 : op = 14#u8
    · exact .inr (.inr ⟨h14, hc⟩)
    have ne {a b : U8} (h : op = a) (hab : a ≠ b) : op = b → False := fun h' => hab (h.symm.trans h')
    by_cases h2 : op = 2#u8
    · rcases code.enter_info.wasm1 st data env .Block with he | ⟨e, s, he⟩
      · exact .inl fun W vis u => step_profile.eq_of_infos vis st data env ctx index op u hc h14
          (fun _ => he) (fun h => (ne h2 (by decide) h).elim) (fun h => (ne h2 (by decide) h).elim)
          (fun h => (ne h2 (by decide) h).elim)
      · exact .inr (.inl ⟨e, s, fun W vis u =>
          step_profile.reject_of_info vis st s data env ctx index op u e hc (.inl ⟨h2, he⟩)⟩)
    by_cases h3 : op = 3#u8
    · rcases code.enter_info.wasm1 st data env .Loop with he | ⟨e, s, he⟩
      · exact .inl fun W vis u => step_profile.eq_of_infos vis st data env ctx index op u hc h14
          (fun h => (ne h3 (by decide) h).elim) (fun _ => he) (fun h => (ne h3 (by decide) h).elim)
          (fun h => (ne h3 (by decide) h).elim)
      · exact .inr (.inl ⟨e, s, fun W vis u =>
          step_profile.reject_of_info vis st s data env ctx index op u e hc (.inr (.inl ⟨h3, he⟩))⟩)
    by_cases h4 : op = 4#u8
    · rcases code.enter_info.wasm1 st data env .Then with he | ⟨e, s, he⟩
      · exact .inl fun W vis u => step_profile.eq_of_infos vis st data env ctx index op u hc h14
          (fun h => (ne h4 (by decide) h).elim) (fun h => (ne h4 (by decide) h).elim) (fun _ => he)
          (fun h => (ne h4 (by decide) h).elim)
      · exact .inr (.inl ⟨e, s, fun W vis u =>
          step_profile.reject_of_info vis st s data env ctx index op u e hc
            (.inr (.inr (.inl ⟨h4, he⟩)))⟩)
    by_cases h17 : op = 17#u8
    · rcases code.call_indirect_info.wasm1 st data env with he | ⟨e, s, he⟩
      · exact .inl fun W vis u => step_profile.eq_of_infos vis st data env ctx index op u hc h14
          (fun h => (ne h17 (by decide) h).elim) (fun h => (ne h17 (by decide) h).elim)
          (fun h => (ne h17 (by decide) h).elim) (fun _ => he)
      · exact .inr (.inl ⟨e, s, fun W vis u =>
          step_profile.reject_of_info vis st s data env ctx index op u e hc
            (.inr (.inr (.inr ⟨h17, he⟩)))⟩)
    exact .inl fun W vis u => step_profile.eq_of_infos vis st data env ctx index op u hc h14
      (fun h => (h2 h).elim) (fun h => (h3 h).elim) (fun h => (h4 h).elim) (fun h => (h17 h).elim)

/-- A returned Wasm 1.0 step returns the same under Wasm 2.0, or it is a rejection that the empty
visitor also reaches. -/
theorem code.step_profile.wasm1 {V : Type} (visitor : code.OpVisitor V) (st : code.BodyState)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (op : U8) (w : V) r
    (h : code.step_profile visitor st data env ctx index .Wasm1 op w = .ok r) :
    code.step_profile visitor st data env ctx index .Wasm2 op w = .ok r ∨
      (r.1 ≠ .Ok () ∧ ∃ e s, code.step_profile code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        st data env ctx index .Wasm1 op () = .ok (.Err e, s, ())) := by
  rcases step_profile.cases st data env ctx index op with hall | ⟨e, s, hall⟩ | ⟨rfl, hc⟩
  · exact .inl ((hall _ visitor w).symm.trans h)
  · rw [hall] at h
    simp only [ok.injEq] at h
    subst r
    exact .inr ⟨by simp, e, s, hall _ _ _⟩
  · rw [step_br_table _ _ _ _ _ _ _ _ hc] at h
    rw [step_br_table _ _ _ _ _ _ _ _ rfl]
    rcases code.branch_table_with.wasm1 visitor st data env w r h with h2 | ⟨hne, e, s, he⟩
    · exact .inl h2
    · exact .inr ⟨hne, e, s, by rw [step_br_table _ _ _ _ _ _ _ _ hc]; exact he⟩

/-- The Wasm 1.0 step returns whenever the Wasm 2.0 step does. -/
theorem code.step_profile.wasm1_returns {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (op : U8) (w : V) r
    (h : code.step_profile visitor st data env ctx index .Wasm2 op w = .ok r) :
    ∃ r', code.step_profile visitor st data env ctx index .Wasm1 op w = .ok r' := by
  rcases step_profile.cases st data env ctx index op with hall | ⟨e, s, hall⟩ | ⟨rfl, hc⟩
  · exact ⟨r, (hall _ visitor w).trans h⟩
  · exact ⟨_, hall _ _ _⟩
  · rw [step_br_table _ _ _ _ _ _ _ _ rfl] at h
    rw [step_br_table _ _ _ _ _ _ _ _ hc]
    exact code.branch_table_with.wasm1_returns visitor st data env w r h

private theorem body_wasm1 {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (w : V) (st : code.BodyState) cf
    (h : Wasm2.Visitor.body visitor data env ctx index .Wasm1 w st = .ok cf) :
    Wasm2.Visitor.body visitor data env ctx index .Wasm2 w st = .ok cf ∨
      (∃ e w', cf = .done (.Err e, w')) ∧ ∃ e, Wasm2.Visitor.body
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx index .Wasm1 () st =
          .ok (.done (.Err e, ())) := by
  unfold Wasm2.Visitor.body code.body_loop_loop.body at h ⊢
  simp only [alloc.vec.Vec.is_empty, bind_ok] at h ⊢
  by_cases he : st.core.ctrls.val = []
  · left; simpa [he] using h
  · simp only [he, List.isEmpty_iff, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e =>
      left
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using h
    | Ok pair =>
      obtain ⟨op, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨⟨r1, s1, w1⟩, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      rcases code.step_profile.wasm1 visitor _ data env ctx index op w _ hs with h2 | ⟨hne, e, s, he⟩
      · left
        rw [h2]
        simpa using h
      · right
        cases r1 with
        | Ok u => exact absurd rfl hne
        | Err e1 =>
          refine ⟨⟨e1, w1, ?_⟩, e, ?_⟩
          · simpa [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              using h.symm
          · simp [he, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

private theorem body_wasm1_returns {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (w : V) (st : code.BodyState) cf
    (h : Wasm2.Visitor.body visitor data env ctx index .Wasm2 w st = .ok cf) :
    ∃ cf', Wasm2.Visitor.body visitor data env ctx index .Wasm1 w st = .ok cf' ∧
      (cf' = cf ∨ ∃ e w', cf' = .done (.Err e, w')) := by
  unfold Wasm2.Visitor.body code.body_loop_loop.body at h ⊢
  simp only [alloc.vec.Vec.is_empty, bind_ok] at h ⊢
  by_cases he : st.core.ctrls.val = []
  · exact ⟨cf, by simpa [he] using h, .inl rfl⟩
  · simp only [he, List.isEmpty_iff, if_false] at h ⊢
    obtain ⟨r, hr, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    rw [hr]
    cases r with
    | Err e => exact ⟨cf, by simpa [core.result.Result.Insts.CoreOpsTry.branch] using h, .inl rfl⟩
    | Ok pair =>
      obtain ⟨op, pos⟩ := pair
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at h ⊢
      obtain ⟨x2, hs, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
      obtain ⟨x1, h1⟩ := code.step_profile.wasm1_returns visitor _ data env ctx index op w x2 hs
      rw [h1]
      rcases code.step_profile.wasm1 visitor _ data env ctx index op w x1 h1 with h2 | ⟨hne, _⟩
      · have he : x1 = x2 := by rw [h2] at hs; simpa using hs
        subst he
        exact ⟨cf, by simpa using h, .inl rfl⟩
      · obtain ⟨r1, s1, w1⟩ := x1
        cases r1 with
        | Ok u => exact absurd rfl hne
        | Err e1 =>
          exact ⟨_, by simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual], .inr ⟨e1, w1, rfl⟩⟩

private theorem body_loop_unfold {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (profile : ValidationProfile) (w : V)
    (st : code.BodyState) :
    code.body_loop_loop visitor data env ctx index profile w st =
      (do
        let cf ← Wasm2.Visitor.body visitor data env ctx index profile w st
        match cf with
        | .cont (u, s) => code.body_loop_loop visitor data env ctx index profile u s
        | .done res => .ok res) := by
  conv_lhs => unfold code.body_loop_loop; rw [loop]
  congr 1
  funext cf
  cases cf <;> rfl

/-- A returned Wasm 1.0 body loop returns the same under Wasm 2.0, or it is a rejection that the
empty visitor also reaches. -/
theorem code.body_loop_loop.wasm1 {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ∀ (n : Nat) (st : code.BodyState) (w : V) r, Usize.max - st.core.pos.val = n →
      Control.Shape st.core → st.blocks.val.length = st.core.ctrls.val.length →
      st.blocks.val.length ≤ st.core.pos.val + 1 →
      code.body_loop_loop visitor data env ctx index .Wasm1 w st = .ok r →
      code.body_loop_loop visitor data env ctx index .Wasm2 w st = .ok r ∨
        (r.1 ≠ .Ok () ∧ ∃ e, code.body_loop_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
          data env ctx index .Wasm1 () st = .ok (.Err e, ())) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro st w r hn hs halign hbound h
  rw [body_loop_unfold] at h
  obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  rcases body_wasm1 visitor data env ctx index w st cf hb with h2 | ⟨⟨e, w', rfl⟩, e', he⟩
  · cases cf with
    | done res =>
      left
      rw [body_loop_unfold, h2]
      simpa using ht
    | cont pair =>
      obtain ⟨w1, s⟩ := pair
      obtain ⟨ecf, hw, ho⟩ := Wasm2.Visitor.body.transfer visitor
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env ctx ctx rfl
        index .Wasm1 st w () _ hb trivial
      have hp := code.body_loop_loop.body.total code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        FullVisitor.empty_total data env ctx index .Wasm1 st () hdata hs halign hbound
      simp only [Wasm2.Visitor.body] at hw
      rw [hw, WP.spec_ok] at hp
      cases ecf with
      | done p => simp [Wasm2.Visitor.bodyObserve] at ho
      | cont p =>
        obtain ⟨u, s'⟩ := p
        cases u
        simp only [Wasm2.Visitor.bodyObserve, ControlFlow.cont.injEq] at ho
        subst s'
        obtain ⟨hinv, hdecr⟩ := hp
        dsimp only at hinv hdecr
        rcases ih (Usize.max - s.core.pos.val) (by omega) s w1 r rfl hinv.1 hinv.2.1 hinv.2.2 ht
          with h3 | ⟨hne, e, he⟩
        · left
          rw [body_loop_unfold, h2]
          simpa using h3
        · right
          refine ⟨hne, e, ?_⟩
          rw [body_loop_unfold]
          simp only [Wasm2.Visitor.body]
          rw [hw]
          simpa using he
  · simp only [ok.injEq] at ht
    subst r
    right
    refine ⟨by simp, e', ?_⟩
    rw [body_loop_unfold, he]
    simp

/-- The Wasm 1.0 body loop returns whenever the Wasm 2.0 body loop does. -/
theorem code.body_loop_loop.wasm1_returns {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32)
    (hdata : data.length ≤ limits.MAX_FUNCTION_BYTES.val) :
    ∀ (n : Nat) (st : code.BodyState) (w : V) r, Usize.max - st.core.pos.val = n →
      Control.Shape st.core → st.blocks.val.length = st.core.ctrls.val.length →
      st.blocks.val.length ≤ st.core.pos.val + 1 →
      code.body_loop_loop visitor data env ctx index .Wasm2 w st = .ok r →
      ∃ r', code.body_loop_loop visitor data env ctx index .Wasm1 w st = .ok r' := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro st w r hn hs halign hbound h
  rw [body_loop_unfold] at h
  obtain ⟨cf, hb, ht⟩ := ResultFacts.bind_ok_inv _ _ _ h
  obtain ⟨cf', h1, hcf⟩ := body_wasm1_returns visitor data env ctx index w st cf hb
  rcases hcf with hcf | ⟨e, w', rfl⟩
  · rw [hcf] at h1
    cases cf with
    | done res => exact ⟨res, by rw [body_loop_unfold, h1]; simp⟩
    | cont pair =>
      obtain ⟨w1, s⟩ := pair
      obtain ⟨ecf, hw, ho⟩ := Wasm2.Visitor.body.transfer visitor
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_accepts data env ctx ctx rfl
        index .Wasm2 st w () _ hb trivial
      have hp := code.body_loop_loop.body.total code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
        FullVisitor.empty_total data env ctx index .Wasm2 st () hdata hs halign hbound
      simp only [Wasm2.Visitor.body] at hw
      rw [hw, WP.spec_ok] at hp
      cases ecf with
      | done p => simp [Wasm2.Visitor.bodyObserve] at ho
      | cont p =>
        obtain ⟨u, s'⟩ := p
        simp only [Wasm2.Visitor.bodyObserve, ControlFlow.cont.injEq] at ho
        subst s'
        obtain ⟨hinv, hdecr⟩ := hp
        dsimp only at hinv hdecr
        obtain ⟨r', hr'⟩ := ih (Usize.max - s.core.pos.val) (by omega) s w1 r rfl hinv.1 hinv.2.1
          hinv.2.2 ht
        exact ⟨r', by rw [body_loop_unfold, h1]; simpa using hr'⟩
  · exact ⟨(.Err e, w'), by rw [body_loop_unfold, h1]; simp⟩

private theorem validate_unfold {V : Type} (visitor : code.OpVisitor V) (data : Slice U8)
    (env : metadata.Env) (ctx : code.Context) (index : U32) (profile : ValidationProfile) (w : V) :
    code.validate_body_with visitor data env ctx index profile w =
      if Slice.len data > limits.MAX_FUNCTION_BYTES then .ok (.Err .BodyTooLarge, w) else (do
        let r ← code.initial_state env index
        match r with
        | .Ok st => code.body_loop_loop visitor data env ctx index profile w st
        | .Err e => .ok (.Err e, w)) := by
  unfold code.validate_body_with
  dsimp only
  split
  · rfl
  · congr 1
    funext r
    cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, code.body_loop]

/-- A returned Wasm 1.0 body validation returns the same under Wasm 2.0, or it is a rejection that
the empty visitor also reaches. -/
theorem code.validate_body_with.wasm1 {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (w : V) r
    (h : code.validate_body_with visitor data env ctx index .Wasm1 w = .ok r) :
    code.validate_body_with visitor data env ctx index .Wasm2 w = .ok r ∨
      (r.1 ≠ .Ok () ∧ ∃ e, code.validate_body_with
        code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor data env ctx index .Wasm1 () = .ok (.Err e, ())) := by
  rw [validate_unfold] at h ⊢
  rw [validate_unfold]
  split at h
  · rename_i hsize
    simp only [hsize, if_true] at ⊢
    left; exact h
  · rename_i hsize
    simp only [hsize, if_false] at ⊢
    obtain ⟨ri, hri, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hp := code.initial_state.total env index
    rw [hri, WP.spec_ok] at hp
    rw [hri]
    simp only [bind_ok]
    cases ri with
    | Err e => left; exact h
    | Ok st =>
      rcases code.body_loop_loop.wasm1 visitor data env ctx index (by scalar_tac) _ st w r rfl
        hp.1 hp.2.1 hp.2.2 h with h2 | ⟨hne, e, he⟩
      · exact .inl h2
      · exact .inr ⟨hne, e, he⟩

/-- The Wasm 1.0 body validation returns whenever the Wasm 2.0 validation does. -/
theorem code.validate_body_with.wasm1_returns {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (w : V) r
    (h : code.validate_body_with visitor data env ctx index .Wasm2 w = .ok r) :
    ∃ r', code.validate_body_with visitor data env ctx index .Wasm1 w = .ok r' := by
  rw [validate_unfold] at h ⊢
  split at h
  · rename_i hsize
    simp only [hsize, if_true]
    exact ⟨_, rfl⟩
  · rename_i hsize
    simp only [hsize, if_false]
    obtain ⟨ri, hri, h⟩ := ResultFacts.bind_ok_inv _ _ _ h
    have hp := code.initial_state.total env index
    rw [hri, WP.spec_ok] at hp
    rw [hri]
    simp only [bind_ok]
    cases ri with
    | Err e => exact ⟨_, rfl⟩
    | Ok st =>
      exact code.body_loop_loop.wasm1_returns visitor data env ctx index (by scalar_tac) _ st w r rfl
        hp.1 hp.2.1 hp.2.2 h

/-- An accepted Wasm 1.0 body validation is the accepted Wasm 2.0 validation. -/
theorem code.validate_body_with.wasm1_accepted {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (w w' : V)
    (h : code.validate_body_with visitor data env ctx index .Wasm1 w = .ok (.Ok (), w')) :
    code.validate_body_with visitor data env ctx index .Wasm2 w = .ok (.Ok (), w') := by
  rcases code.validate_body_with.wasm1 visitor data env ctx index w _ h with h2 | ⟨hne, _⟩
  · exact h2
  · exact absurd rfl hne

/-- Once the empty-visitor Wasm 1.0 validator accepts a body, every visitor gets the same result
under both profiles. -/
theorem code.validate_body_with.wasm1_of_accepted {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.Env) (ctx : code.Context) (index : U32) (w : V) r
    (haccepted : code.bodyCore data env ctx.locals ctx.results index .Wasm1 = .ok (.Ok ()))
    (h : code.validate_body_with visitor data env ctx index .Wasm2 w = .ok r) :
    code.validate_body_with visitor data env ctx index .Wasm1 w = .ok r := by
  obtain ⟨r', h1⟩ := code.validate_body_with.wasm1_returns visitor data env ctx index w r h
  rcases code.validate_body_with.wasm1 visitor data env ctx index w r' h1 with h2 | ⟨_, e, he⟩
  · rw [h2] at h
    simp only [ok.injEq] at h
    rw [h1, h]
  · rw [← code.validate_body_with.eq_core, he] at haccepted
    simp at haccepted

end Itasca
