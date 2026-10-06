import Itasca.ModuleCodeEntry

open Aeneas Aeneas.Std

namespace Itasca.ModuleCode

/-- Entry framing is independent of local declarations and body validation. -/
def Extent (data : Slice U8) (start content finish : Usize) : Prop :=
  ∃ size, Leb128.Decoded data start size content ∧
    finish.val = content.val + size.val ∧ finish.val ≤ data.length

theorem Extent.span {data start content finish} (h : Extent data start content finish) :
    start.val < content.val ∧ content.val ≤ finish.val ∧ finish.val ≤ data.length := by
  obtain ⟨size, hs, hn, hb⟩ := h
  have := hs.span
  omega

theorem decoded_unique {data start x y next last}
    (hx : Leb128.Decoded data start x next) (hy : Leb128.Decoded data start y last) :
    x = y ∧ next = last := by
  have h := (reader.read_u32_leb.complete data start x next hx).symm.trans
    (reader.read_u32_leb.complete data start y last hy)
  simpa using h

def Section (data : Slice U8) (start : Usize) (env : module.Env) (cs : module.CodeSection) : Prop :=
  ∃ content, ModuleBinary.SectionHeader data start 10#u8 content cs.end ∧
    Leb128.Decoded data content cs.count cs.entries ∧
    cs.count.val = env.func_type_indices.val.length

def SectionPost (data : Slice U8) (start : Usize) (env : module.Env) :
    core.result.Result (Option module.CodeSection) error.Error → Prop
  | .Ok none => env.func_type_indices.val = []
  | .Ok (some cs) => Section data start env cs
  | .Err _ => True

end ModuleCode

@[step]
theorem module.code_entry_extent.spec (data : Slice U8) (pos : Usize) :
    module.code_entry_extent data pos ⦃ r => match r with
      | .Ok (content, finish) => ModuleCode.Extent data pos content finish
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  rw [module.code_entry_extent, hr]
  cases r with
  | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨size, content⟩ := pair
      have hs := hp.span
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      step
      obtain ⟨r, hh, hhpost⟩ := WP.spec_imp_exists (module.have_bytes.spec data content n hs.2.2)
      rw [hh]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok u =>
          cases u
          have hb := hhpost.1.mp rfl
          simp
          step
          exact ⟨size, hp, by scalar_tac, by scalar_tac⟩

/-- Both paths read the same declared entry size, so a successful validating
callback ends at the independently checked framing boundary. -/
theorem module.code_entry_extent.frames (data : Slice U8) (pos content finish : Usize)
    (env : module.Env) (index next : Usize) (hbound : CodeEntry.Bounds env)
    (hext : ModuleCode.Extent data pos content finish)
    (hentry : module.validate_code_entry data pos env index = .ok (.Ok next)) : finish = next := by
  obtain ⟨⟨r, v⟩, hr, hp⟩ := WP.spec_imp_exists (module.validate_code_entry_with.pipeline
    code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor FullVisitor.empty_total data pos env index () hbound)
  have he : r = .Ok next := by simpa [module.validate_code_entry, hr] using hentry
  obtain ⟨w⟩ := hp next he
  obtain ⟨size, hs, hn, _⟩ := hext
  obtain ⟨heq, hp⟩ := ModuleCode.decoded_unique hs w.header
  apply UScalar.eq_of_val_eq
  have := w.extent
  rw [← heq, ← hp] at this
  omega

@[step]
theorem module.no_code_section.spec (env : module.Env) :
    module.no_code_section env ⦃ r =>
      match r with | .Ok opt => opt = none ∧ env.func_type_indices.val = [] | .Err _ => True ⦄ := by
  simp [module.no_code_section, alloc.vec.Vec.is_empty]
  split <;> simp_all

@[step]
theorem module.code_section.spec (data : Slice U8) (pos : Usize) (env : module.Env) :
    module.code_section data pos env ⦃ ModuleCode.SectionPost data pos env ⦄ := by
  unfold module.code_section
  dsimp only
  split
  · apply WP.spec_mono (module.no_code_section.spec env)
    intro r hr
    cases r with
    | Err => trivial
    | Ok opt => simpa [hr.1, ModuleCode.SectionPost] using hr.2
  · obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.read_section_header.spec data pos)
    rw [hr]
    cases r with
    | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ModuleCode.SectionPost]
    | Ok tuple =>
        obtain ⟨id, content, finish⟩ := tuple
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        split
        · rename_i hid
          have hid' : id = 10#u8 := by
            apply UScalar.eq_of_val_eq
            simpa [module.SECTION_CODE] using hid
          obtain ⟨r, hl, hlpost⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data content)
          rw [hl]
          cases r with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from, ModuleCode.SectionPost]
          | Ok pair =>
              obtain ⟨count, entries⟩ := pair
              simp
              step
              split
              · rename_i hcount
                simp only [WP.spec_ok, ModuleCode.SectionPost]
                exact ⟨content, by simpa [hid'] using hp, hlpost, by scalar_tac⟩
              · simp [ModuleCode.SectionPost]
        · apply WP.spec_mono (module.no_code_section.spec env)
          intro r hr
          cases r with
          | Err => trivial
          | Ok opt => simpa [hr.1, ModuleCode.SectionPost] using hr.2

end Itasca
