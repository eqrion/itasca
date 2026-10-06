import Itasca.ModuleCode

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

/-- Termination of code callbacks is independent of whether an override validates
its entries. A deferred compiler can satisfy this before any worker finishes. -/
structure HooksTotal {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (env : module.Env) : Prop where
  need_bytes : ∀ v finish, ∃ r v', visitor.on_need_bytes v finish = .ok (r, v')
  entry : ∀ v i start content finish, Extent data start content finish →
    ∃ r v', visitor.on_code_entry v data env i start content finish = .ok (r, v')

theorem VisitorContract.total {V : Type} {visitor : module.CodeVisitor V} {data env}
    (h : VisitorContract visitor data env) : HooksTotal visitor data env := by
  refine ⟨h.need_bytes, ?_⟩
  intro v i start content finish he
  obtain ⟨⟨r, v'⟩, hr, _⟩ := WP.spec_imp_exists (h.entry v i start content finish he)
  exact ⟨r, v', hr⟩

end ModuleCode

/-- Only cursor bounds and callback termination are needed for the framing
loop to return. In particular, entry typing is not a totality premise. -/
theorem module.validate_code_entries_with_loop.total_spec {V : Type}
    (visitor : module.CodeVisitor V) (data : Slice U8) (env : module.Env)
    (v : V) (pos index : Usize) (htotal : ModuleCode.HooksTotal visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ data.length) (hindex : index.val ≤ env.func_type_indices.val.length) :
    module.validate_code_entries_with_loop visitor data env v pos index ⦃ r =>
      ∀ finish, r.1 = .Ok finish → finish.val ≤ data.length ⦄ := by
  unfold module.validate_code_entries_with_loop
  apply loop.spec_decr_nat (fun s => env.func_type_indices.val.length - s.2.2.val)
    (fun s => s.2.1.val ≤ data.length ∧ s.2.2.val ≤ env.func_type_indices.val.length)
  · rintro ⟨w, q, i⟩ ⟨hq, hi⟩
    dsimp only at hq hi
    unfold module.validate_code_entries_with_loop.body
    dsimp only
    split
    · simpa using hq
    · rename_i hmore
      have himore : i.val < env.func_type_indices.val.length := by scalar_tac
      have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
        have := ModuleCode.module_room
        simp only [limits.MAX_LEB_BYTES]
        scalar_tac
      step
      obtain ⟨reply, w1, hneed⟩ := htotal.need_bytes w i2
      rw [hneed]
      cases reply with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
        cases u
        obtain ⟨r, hframe, hframepost⟩ := WP.spec_imp_exists (module.code_entry_extent.spec data q)
        simp [core.result.Result.Insts.CoreOpsTry.branch, hframe]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨content, finish⟩ := pair
          obtain ⟨reply, w2, hneed2⟩ := htotal.need_bytes w1 finish
          simp [hneed2]
          cases reply with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
            cases u
            obtain ⟨reply, w3, hentry⟩ := htotal.entry w2 i q content finish hframepost
            simp [hentry]
            cases reply with
            | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok u =>
              cases u
              simp
              step
              have hfinish := hframepost.span.2.2
              exact ⟨hfinish, by scalar_tac, by scalar_tac⟩
  · exact ⟨hpos, hindex⟩

/-- Arbitrary terminating code hooks cannot introduce a panic or divergence in
the bounded code-section driver, even when they defer all entry validation. -/
theorem module.validate_code_with.total_spec {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V)
    (htotal : ModuleCode.HooksTotal visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length) :
    module.validate_code_with visitor data pos env v ⦃ r =>
      ∀ finish, r.1 = .Ok finish → finish.val ≤ data.length ⦄ := by
  have hheader : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
    have hs : limits.MAX_CODE_HEADER_BYTES ⦃ x => x = 11#usize ⦄ := by
      unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
      step*
    obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
    exact hx
  have hroom : pos.val + (11#usize).val ≤ Usize.max := by
    have := ModuleCode.module_room
    scalar_tac
  rw [module.validate_code_with, hheader]
  simp only [bind_ok]
  step
  obtain ⟨reply, w, hneed⟩ := htotal.need_bytes v i1
  rw [hneed]
  cases reply with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
    cases u
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.code_section.spec data pos env)
    simp [core.result.Result.Insts.CoreOpsTry.branch, hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok opt =>
      cases opt with
      | none => simpa using hpos
      | some cs =>
        have hentries : cs.entries.val ≤ data.length := by
          obtain ⟨content, _, hd, _⟩ := hp
          exact hd.span.2.2
        obtain ⟨⟨r, w'⟩, he, _⟩ := WP.spec_imp_exists
          (module.validate_code_entries_with_loop.total_spec visitor data env w cs.entries 0#usize
            htotal hsize hentries (by simp))
        simp [module.validate_code_entries_with, he]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok finish =>
          have hend : cs.end.val ≤ data.length := by
            obtain ⟨content, hh, _, _⟩ := hp
            exact hh.span.2.2
          simp
          split <;> simp_all

theorem module.validate_code_with.total_with_hooks {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V)
    (htotal : ModuleCode.HooksTotal visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length) :
    ∃ r, module.validate_code_with visitor data pos env v = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (module.validate_code_with.total_spec visitor data pos env v htotal hsize hpos)
  exact ⟨r, hr⟩

end Itasca
