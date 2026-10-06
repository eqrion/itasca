import Itasca.ModuleCodeEntryComplete
import Itasca.ModuleCode
import Itasca.ModuleFramingComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleBinary

theorem At.code_extent {data pos entry next} (h : At CodeEncoding data pos entry next) :
    ∃ first, ModuleCode.Extent data pos first next := by
  obtain ⟨bytes, he, hs⟩ := h
  obtain ⟨sizeBytes, localBytes, bodyBytes, hsize, _, _, rfl⟩ := he
  obtain ⟨bodyStart, hprefix, hbody⟩ := hs.split
  obtain ⟨first, hhead, hlocals⟩ := hprefix.split
  let count : U32 := U32.ofNatCore (localBytes.length + bodyBytes.length) (by have := hsize.value_lt; scalar_tac)
  have hc : count.val = localBytes.length + bodyBytes.length := by simp [count]
  exact ⟨first, count, hhead.u32_decoded count (by simpa [hc] using hsize),
    by have := hlocals.length; have := hbody.length; omega, hs.bound⟩

end Itasca.ModuleBinary

namespace Itasca

open ModuleBinary

theorem module.code_entry_extent.complete (data : Slice U8) (pos first next : Usize)
    (h : ModuleCode.Extent data pos first next) :
    module.code_entry_extent data pos = .ok (.Ok (first, next)) := by
  obtain ⟨count, hc, hn, hb⟩ := h
  have hs : module.code_entry_extent data pos ⦃ r => r = .Ok (first, next) ⦄ := by
    simp [module.code_entry_extent, reader.read_u32_leb.complete data pos count first hc,
      core.result.Result.Insts.CoreOpsTry.branch]
    step
    rw [module.have_bytes.complete data first n (by scalar_tac)]
    simp only [bind_ok]
    step*
    congr 3
    apply UScalar.eq_of_val_eq
    scalar_tac
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- The concrete validating code visitor accepts each bounded, typed entry. -/
theorem module.validate_code_entries_with_loop.complete
    (data : Slice U8) (env : module.Env) (pos index next : Usize) (entries : List Code)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (hcount : index.val + entries.length = env.func_type_indices.val.length)
    (htyped : List.Forall₂ (CodeEntry.Typed env) (env.func_type_indices.val.drop index.val) entries)
    (hbytes : At (Rep CodeEncodingWithinLimits) data pos entries next) :
    module.validate_code_entries_with_loop module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor
      data env () pos index = .ok (.Ok next, ()) := by
  induction entries generalizing pos index with
  | nil =>
    have hp := hbytes.rep_nil
    have hi : index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
    unfold module.validate_code_entries_with_loop
    rw [loop]
    simp [module.validate_code_entries_with_loop.body, hi, hp]
  | cons entry entries ih =>
    have hi : index.val < env.func_type_indices.val.length := by
      simp only [List.length_cons] at hcount; omega
    rw [List.drop_eq_getElem_cons hi] at htyped
    cases htyped with
    | cons ht hts =>
      obtain ⟨middle, hentry, hrest⟩ := hbytes.rep_cons
      obtain ⟨first, hext⟩ := (show At CodeEncoding data pos entry middle from
        ⟨hentry.choose, hentry.choose_spec.1.encoding, hentry.choose_spec.2⟩).code_extent
      have hr := module.code_entry_extent.complete data pos first middle hext
      have he := module.validate_code_entry.complete data pos env index entry middle hi ht henv hbound hentry
      have hstop : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by scalar_tac
      obtain ⟨need, hneed, _⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := pos) (y := limits.MAX_LEB_BYTES)
          (by have := hbytes.span; have := ModuleCode.module_room; simp only [limits.MAX_LEB_BYTES]; scalar_tac))
      obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      have hrec := ih middle j
        (by simp only [List.length_cons] at hcount; scalar_tac)
        (by simpa [hjval] using hts) hrest
      unfold module.validate_code_entries_with_loop
      rw [loop]
      simpa [module.validate_code_entries_with_loop.body, hstop, hneed, hr, hj, he,
        module.CodeVisitor.on_code_entry.default, module.CodeVisitor.on_need_bytes.default,
        core.result.Result.Insts.CoreOpsTry.branch,
        module.validate_code_entries_with_loop] using hrec

theorem module.validate_code_entries_with.complete
    (data : Slice U8) (env : module.Env) (pos next : Usize) (entries : List Code)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (htyped : List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val entries)
    (hbytes : At (Rep CodeEncodingWithinLimits) data pos entries next) :
    module.validate_code_entries_with module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor
      data pos env () = .ok (.Ok next, ()) := by
  exact module.validate_code_entries_with_loop.complete data env pos 0#usize next entries hsize henv hbound
    (by simpa using htyped.length_eq.symm) (by simpa using htyped) hbytes

/-- Exact independently encoded code sections produce the corresponding entry interval. -/
theorem module.code_section.complete_present (data : Slice U8) (pos next : Usize)
    (env : module.Env) (entries : List Code)
    (hcount : entries.length = env.func_type_indices.val.length)
    (hbytes : At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits)) data pos entries next) :
    ∃ cs, module.code_section data pos env = .ok (.Ok (some cs)) ∧
      cs.end = next ∧ At (Rep CodeEncodingWithinLimits) data cs.entries entries next := by
  obtain ⟨first, hh, hv⟩ := hbytes.section_split
  obtain ⟨count, start, hc, hleb, hentries⟩ := hv.vector_split
  have hp : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
  have hs : module.code_section data pos env ⦃ r =>
      ∃ cs, r = .Ok (some cs) ∧ cs.end = next ∧
        At (Rep CodeEncodingWithinLimits) data cs.entries entries next ⦄ := by
    simp [module.code_section, hp, module.read_section_header.complete data pos 10#u8 first next hh,
      reader.read_u32_leb.complete data first count start hleb,
      module.SECTION_CODE, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have he : i1 = alloc.vec.Vec.len env.func_type_indices := by
      apply UScalar.eq_of_val_eq
      scalar_tac
    simp [he]
    exact hentries
  obtain ⟨r, hr, cs, rfl, hend, hentries⟩ := WP.spec_imp_exists hs
  exact ⟨cs, hr, hend, hentries⟩

/-- An absent code section is justified by EOF or a complete non-code header.
The header premise matters because the implementation checks its extent before
examining its section ID. -/
def ModuleCode.AbsentAt (data : Slice U8) (pos : Usize) : Prop :=
  pos.val = data.length ∨
    ∃ id first last, SectionHeader data pos id first last ∧ id ≠ 10#u8

theorem module.code_section.complete_absent (data : Slice U8) (pos : Usize)
    (env : module.Env) (hempty : env.func_type_indices.val = [])
    (hstop : ModuleCode.AbsentAt data pos) :
    module.code_section data pos env = .ok (.Ok none) := by
  have hn : module.no_code_section env = .ok (.Ok none) := by
    simp [module.no_code_section, alloc.vec.Vec.is_empty, hempty]
  rcases hstop with hp | ⟨id, first, last, hh, hid⟩
  · have he : pos ≥ Slice.len data := by scalar_tac
    simp [module.code_section, he, hn]
  · have he : ¬ pos ≥ Slice.len data := by have := hh.span; scalar_tac
    have hi : id.val ≠ 10 := by intro hx; apply hid; apply UScalar.eq_of_val_eq; simpa using hx
    simp [module.code_section, he, module.read_section_header.complete data pos id first last hh,
      module.SECTION_CODE, hi, hn, core.result.Result.Insts.CoreOpsTry.branch]

private theorem header_size : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
  have hs : limits.MAX_CODE_HEADER_BYTES ⦃ x => x = 11#usize ⦄ := by
    unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
    step*
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

private theorem header_room (data : Slice U8) (pos : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) (hp : pos.val ≤ data.length) :
    ∃ need : Usize, (pos + 11#usize : Result Usize) = Result.ok need := by
  have hroom := ModuleCode.module_room
  obtain ⟨need, hn, _⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := pos) (y := 11#usize) (by scalar_tac))
  exact ⟨need, hn⟩

/-- Default code validation succeeds on the exact bounded, declaratively typed entries. -/
theorem module.validate_code.complete_present
    (data : Slice U8) (env : module.Env) (pos next : Usize) (entries : List Code)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (henv : Wasm1.Environment env) (hbound : CodeEntry.Bounds env)
    (htyped : List.Forall₂ (CodeEntry.Typed env) env.func_type_indices.val entries)
    (hbytes : At (SectionEncoding 10#u8 (VecEncoding CodeEncodingWithinLimits)) data pos entries next) :
    module.validate_code data pos env = .ok (.Ok next) := by
  obtain ⟨cs, hcs, hend, he⟩ := module.code_section.complete_present data pos next env entries
    htyped.length_eq.symm hbytes
  have hv := module.validate_code_entries_with.complete data env cs.entries next entries
    hsize henv hbound htyped he
  obtain ⟨need, hn⟩ := header_room data pos hsize (by have := hbytes.span; omega)
  simp only [module.validate_code, module.validate_code_with, header_size, bind_ok]
  simp [hn, module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor,
    module.CodeVisitor.on_need_bytes.default, hcs, hv, hend,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem module.validate_code.complete_absent
    (data : Slice U8) (env : module.Env) (pos : Usize)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hempty : env.func_type_indices.val = [])
    (hstop : ModuleCode.AbsentAt data pos) :
    module.validate_code data pos env = .ok (.Ok pos) := by
  have hp : pos.val ≤ data.length := by
    rcases hstop with he | ⟨_, _, _, hh, _⟩
    · omega
    · have := hh.span; omega
  obtain ⟨need, hn⟩ := header_room data pos hsize hp
  simp only [module.validate_code, module.validate_code_with, header_size, bind_ok]
  simp [hn, module.ValidatingCodeVisitor.Insts.ItascaModuleCodeVisitor,
    module.CodeVisitor.on_need_bytes.default,
    module.code_section.complete_absent data pos env hempty hstop,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
