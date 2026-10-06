import Itasca.ModuleCodeSection

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

def EntryAt (env : module.Env) (i : Nat) (entry : ModuleBinary.Code) : Prop :=
  ∃ hi : i < env.func_type_indices.val.length,
    CodeEntry.Typed env env.func_type_indices.val[i] entry ∧
    entry.declared.length ≤ limits.MAX_LOCALS.val

inductive EntriesTyped (env : module.Env) : Nat → List ModuleBinary.Code → Prop where
  | nil (i : Nat) : EntriesTyped env i []
  | cons {i entry entries} : EntryAt env i entry → EntriesTyped env (i + 1) entries →
      EntriesTyped env i (entry :: entries)

theorem EntriesTyped.snoc {env i entries entry}
    (h : EntriesTyped env i entries) (he : EntryAt env (i + entries.length) entry) :
    EntriesTyped env i (entries ++ [entry]) := by
  induction h with
  | nil i => exact .cons (by simpa using he) (.nil _)
  | @cons i first rest hfirst hrest ih =>
    exact .cons hfirst (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he))

theorem entries_at_snoc {data start pos next entries entry}
    (hp : ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data start entries pos)
    (he : ModuleBinary.At ModuleBinary.CodeEncoding data pos entry next) :
    ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data start (entries ++ [entry]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := he
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

theorem EntriesTyped.forall₂ {env i entries}
    (h : EntriesTyped env i entries) (hn : i + entries.length = env.func_type_indices.val.length) :
    List.Forall₂ (CodeEntry.Typed env) (env.func_type_indices.val.drop i) entries := by
  induction h with
  | nil i =>
    have hb : env.func_type_indices.val.length ≤ i := by simpa using hn.symm.le
    simp [List.drop_eq_nil_of_le hb]
  | @cons i entry entries ht hs ih =>
    obtain ⟨hi, ht, _⟩ := ht
    rw [List.drop_eq_getElem_cons hi]
    exact .cons ht (ih (by simp only [List.length_cons] at hn; omega))

/-- Entry overrides are permitted to reject or maintain visitor state, but a
successful handoff must certify the actual entry interval. The default visitor
satisfies this contract by running the checked validator below. -/
structure VisitorContract {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (env : module.Env) : Prop where
  need_bytes : ∀ v finish, ∃ r v', visitor.on_need_bytes v finish = .ok (r, v')
  entry : ∀ v i start content finish, Extent data start content finish →
    visitor.on_code_entry v data env i start content finish ⦃ r =>
      r.1 = .Ok () → CodeEntry.Validated data env i start finish ⦄

theorem default_contract (data : Slice U8) (env : module.Env)
    (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    VisitorContract module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data env := by
  constructor
  · intro v finish
    exact ⟨.Ok (), v, rfl⟩
  · intro v i start content finish hext
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.validate_code_entry.spec data start env i hbound hresults)
    simp only [module.CodeVisitor.on_code_entry.default, hr, bind_ok]
    cases r with
    | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok next =>
        have heq := module.code_entry_extent.frames data start content finish env i next hbound hext hr
        simpa [core.result.Result.Insts.CoreOpsTry.branch, heq] using hp next rfl

theorem module_room : limits.MAX_MODULE_BYTES.val + 11 ≤ Usize.max := by
  simp only [limits.MAX_MODULE_BYTES]
  scalar_tac

end ModuleCode

/-- The actual entries loop validates each defined function exactly once, in
function-section order, and preserves the independently framed byte prefix. -/
theorem module.validate_code_entries_with_loop.spec {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (env : module.Env) (v : V) (pos index : Usize)
    (hvisitor : ModuleCode.VisitorContract visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hpos : pos.val ≤ data.length) (hindex : index.val ≤ env.func_type_indices.val.length) :
    module.validate_code_entries_with_loop visitor data env v pos index ⦃ r =>
      ∀ finish, r.1 = .Ok finish → ∃ entries,
        entries.length = env.func_type_indices.val.length - index.val ∧
        ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data pos entries finish ∧
        ModuleCode.EntriesTyped env index.val entries ⦄ := by
  unfold module.validate_code_entries_with_loop
  apply loop.spec_decr_nat (fun s => env.func_type_indices.val.length - s.2.2.val)
    (fun s => index.val ≤ s.2.2.val ∧ s.2.2.val ≤ env.func_type_indices.val.length ∧
      ∃ entries, entries.length = s.2.2.val - index.val ∧
        ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data pos entries s.2.1 ∧
        ModuleCode.EntriesTyped env index.val entries)
  · rintro ⟨w, q, i⟩ ⟨hstart, hi, entries, hn, he, ht⟩
    dsimp only at hstart hi hn he ht
    have hq := he.span.2
    unfold module.validate_code_entries_with_loop.body
    dsimp only
    split
    · rename_i hstop
      have hdone : i.val = env.func_type_indices.val.length := by scalar_tac
      simp
      exact ⟨entries, by omega, he, ht⟩
    · rename_i hmore
      have himore : i.val < env.func_type_indices.val.length := by scalar_tac
      have hroom : q.val + limits.MAX_LEB_BYTES.val ≤ Usize.max := by
        have := ModuleCode.module_room
        simp only [limits.MAX_LEB_BYTES]
        scalar_tac
      step
      obtain ⟨reply, w1, hneed⟩ := hvisitor.need_bytes w i2
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
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
              obtain ⟨content, finish⟩ := pair
              obtain ⟨reply, w2, hneed2⟩ := hvisitor.need_bytes w1 finish
              simp [hneed2]
              cases reply with
              | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                  cases u
                  obtain ⟨⟨result, w3⟩, hentry, hentrypost⟩ := WP.spec_imp_exists
                    (hvisitor.entry w2 i q content finish hframepost)
                  simp [hentry]
                  cases result with
                  | Err e =>
                      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                  | Ok u =>
                      cases u
                      obtain ⟨entry, hb, hti⟩ := hentrypost rfl
                      simp
                      step
                      refine ⟨?_, ?_, ⟨entries ++ [entry], ?_, ModuleCode.entries_at_snoc he hb, ?_⟩, ?_⟩
                      · scalar_tac
                      · scalar_tac
                      · simp only [List.length_append, List.length_singleton]
                        scalar_tac
                      · apply ht.snoc
                        have heq : index.val + entries.length = i.val := by omega
                        rw [heq]
                        exact hti
                      · scalar_tac
  · exact ⟨le_refl _, hindex, [], by simp,
      ⟨[], .nil, Wasm.BytesAt.nil data pos hpos⟩, .nil _⟩

theorem module.validate_code_entries_with.spec {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V)
    (hvisitor : ModuleCode.VisitorContract visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length) :
    module.validate_code_entries_with visitor data pos env v ⦃ r =>
      ∀ finish, r.1 = .Ok finish → ∃ entries,
        entries.length = env.func_type_indices.val.length ∧
        ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data pos entries finish ∧
        ModuleCode.EntriesTyped env 0 entries ⦄ := by
  simpa [module.validate_code_entries_with] using
    module.validate_code_entries_with_loop.spec visitor data env v pos 0#usize hvisitor hsize hpos (by simp)

end Itasca
