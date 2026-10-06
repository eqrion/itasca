import Itasca.ModuleCodeEntries

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

def Encoding := ModuleBinary.OptionalSectionEncoding 10#u8
  (ModuleBinary.VecEncoding ModuleBinary.CodeEncoding) []

def Validated (data : Slice U8) (start : Usize) (env : module.Env) (finish : Usize) : Prop :=
  ∃ entries, ModuleBinary.At Encoding data start entries finish ∧
    entries.length = env.func_type_indices.val.length ∧ EntriesTyped env 0 entries

theorem Validated.padded {data start env finish} (h : Validated data start env finish) :
    ∃ entries, ModuleBinary.At
      (ModuleBinary.PaddedEncoding 10#u8 (ModuleBinary.VecEncoding ModuleBinary.CodeEncoding) [])
      data start entries finish ∧
      List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val entries := by
  obtain ⟨entries, ⟨bytes, he, hb⟩, hn, ht⟩ := h
  exact ⟨entries, ⟨bytes, ⟨[], bytes, .nil, he, rfl⟩, hb⟩,
    by simpa using ht.forall₂ (by simpa using hn)⟩

theorem Section.encoding {data start env cs entries}
    (h : Section data start env cs)
    (hb : ModuleBinary.At (ModuleBinary.Rep ModuleBinary.CodeEncoding) data cs.entries entries cs.end)
    (hn : entries.length = env.func_type_indices.val.length) :
    ModuleBinary.At Encoding data start entries cs.end := by
  obtain ⟨content, ⟨afterId, size, hid, hsize, hlen, _⟩, hcount, hcountval⟩ := h
  obtain ⟨countBytes, hc, hclen, hcbound, hcenc⟩ := hcount
  obtain ⟨entryBytes, he, hes⟩ := hb
  have payload : Wasm.BytesAt data content (countBytes ++ entryBytes) cs.end :=
    (⟨hc, hclen, hcbound⟩ : Wasm.BytesAt data content countBytes cs.entries).append hes
  obtain ⟨sizeBytes, hs, hslen, hsbound, hsenc⟩ := hsize
  have hsizeval : size.val = (countBytes ++ entryBytes).length := by
    have := payload.length
    omega
  have hpayload : ModuleBinary.VecEncoding ModuleBinary.CodeEncoding entries (countBytes ++ entryBytes) :=
    ⟨countBytes, entryBytes, by simpa [hcountval, hn] using hcenc, he, rfl⟩
  refine ⟨10#u8 :: (sizeBytes ++ (countBytes ++ entryBytes)), .present ?_, ?_⟩
  · exact ⟨sizeBytes, countBytes ++ entryBytes, by simpa [hsizeval] using hsenc, hpayload, rfl⟩
  · simpa using hid.byte.append
      ((⟨hs, hslen, hsbound⟩ : Wasm.BytesAt data afterId sizeBytes content).append payload)

end ModuleCode

/-- The code-section driver is total on bounded module bytes and preserves the
same independently encoded function bodies in function-section order. -/
theorem module.validate_code_with.spec {V : Type} (visitor : module.CodeVisitor V)
    (data : Slice U8) (pos : Usize) (env : module.Env) (v : V)
    (hvisitor : ModuleCode.VisitorContract visitor data env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length) :
    module.validate_code_with visitor data pos env v ⦃ r =>
      ∀ finish, r.1 = .Ok finish → ModuleCode.Validated data pos env finish ⦄ := by
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
  obtain ⟨reply, w, hneed⟩ := hvisitor.need_bytes v i1
  rw [hneed]
  cases reply with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok u =>
      cases u
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.code_section.spec data pos env)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hr]
      cases r with
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok opt =>
          cases opt with
          | none =>
              simp
              exact ⟨[], ⟨[], .absent, Wasm.BytesAt.nil data pos hpos⟩,
                by simp [ModuleCode.SectionPost] at hp; simp [hp], .nil 0⟩
          | some cs =>
              have hentries : cs.entries.val ≤ data.length := by
                obtain ⟨content, _, hd, _⟩ := hp
                exact hd.span.2.2
              obtain ⟨⟨r, w'⟩, he, hepost⟩ := WP.spec_imp_exists
                (module.validate_code_entries_with.spec visitor data cs.entries env w hvisitor hsize hentries)
              simp [he]
              cases r with
              | Err e =>
                  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok finish =>
                  obtain ⟨entries, hn, hb, ht⟩ := hepost finish rfl
                  simp
                  split
                  · rename_i hfinish
                    have heq : finish = cs.end := UScalar.eq_of_val_eq hfinish
                    simp
                    exact ⟨entries, hp.encoding (heq ▸ hb) hn, hn, ht⟩
                  · simp

theorem module.validate_code.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length)
    (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    module.validate_code data pos env ⦃ r =>
      ∀ finish, r = .Ok finish → ModuleCode.Validated data pos env finish ⦄ := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists (module.validate_code_with.spec
    module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor data pos env ()
    (ModuleCode.default_contract data env hbound hresults) hsize hpos)
  simpa [module.validate_code, hr] using hp

theorem module.validate_code.total (data : Slice U8) (pos : Usize) (env : module.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hpos : pos.val ≤ data.length)
    (hbound : CodeEntry.Bounds env)
    (hresults : ∀ ft ∈ env.types.val, ft.results.val.length ≤ 1) :
    ∃ r, module.validate_code data pos env = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (module.validate_code.spec data pos env hsize hpos hbound hresults)
  exact ⟨r, hr⟩

end Itasca
