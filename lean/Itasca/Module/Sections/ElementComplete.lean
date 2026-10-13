import Itasca.Module.Sections.ElementHeaderComplete
import Itasca.Module.Sections.Element
import Itasca.Module.Readers.BasicComplete
import Itasca.Module.Const.ParserComplete

open Aeneas Aeneas.Std



namespace Itasca

open ModuleBinary ModuleSections

theorem module.decode_func_indices_loop.complete (data : Slice U8) (env : module.Env)
    (count : U32) (out : alloc.vec.Vec U32) (pos : Usize) (i : U32)
    (indices : List U32) (next : Usize)
    (hb : At (Rep IndexEncoding) data pos indices next)
    (hc : i.val + indices.length = count.val)
    (hv : ∀ idx ∈ indices, idx.val < env.func_types.val.length)
    (hcap : out.val.length + indices.length ≤ Usize.max) :
    ∃ result, module.decode_func_indices_loop data env count out pos i = .ok (.Ok (result, next)) ∧
      result.val = out.val ++ indices := by
  induction indices generalizing out pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨out, ?_, by simp⟩
    unfold module.decode_func_indices_loop
    rw [loop]
    simp [module.decode_func_indices_loop.body, hstop, he]
  | cons idx indices ih =>
    obtain ⟨middle, hidx, hrest⟩ := hb.rep_cons
    have hread := hidx.read_index
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hnidx : ¬ env.func_types.val.length ≤ idx.val := Nat.not_le.mpr (hv idx (by simp))
    have hvalid : ¬ UScalar.cast .Usize idx ≥ alloc.vec.Vec.len env.func_types := by
      have := hv idx (by simp); scalar_tac
    obtain ⟨updated, hpush, hvals⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out idx (by simp only [List.length_cons] at hcap; omega))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    obtain ⟨result, hloop, hresult⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by intro ix hx; exact hv ix (by simp [hx]))
      (by simp only [hvals, List.length_append, List.length_singleton]; simp only [List.length_cons] at hcap; omega)
    refine ⟨result, ?_, by simpa [hvals, List.append_assoc] using hresult⟩
    unfold module.decode_func_indices_loop at hloop ⊢
    rw [loop]
    simpa [module.decode_func_indices_loop.body, hmore, hread, hnidx,
      hpush, hj, core.result.Result.Insts.CoreOpsTry.branch, lift] using hloop

theorem module.decode_func_indices.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (indices : List U32) (next : Usize)
    (hb : At (VecEncoding IndexEncoding) data pos indices next)
    (hv : ∀ idx ∈ indices, idx.val < env.func_types.val.length) :
    ∃ result, module.decode_func_indices data pos env = .ok (.Ok (result, next)) ∧
      result.val = indices := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, hp⟩ := module.decode_func_indices_loop.complete
    data env count (alloc.vec.Vec.new _) middle 0#u32 indices next hentries
    (by simpa using hc.symm) hv (by simp; scalar_tac)
  refine ⟨result, ?_, by simpa using hp⟩
  simp [module.decode_func_indices, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]


private theorem element_raw_valid_caches {env result entry}
    (h : ElementValidRaw env entry)
    (hf : result.func_types = env.func_types) (hg : result.global_types = env.global_types)
    (hn : result.num_imported_globals = env.num_imported_globals)
    (ht : result.table_types = env.table_types) : ElementValidRaw result entry := by
  obtain ⟨hm, hi⟩ := h
  constructor
  · cases hmode : entry.mode with
    | Passive | Declarative => trivial
    | Active index offset =>
      rw [hmode] at hm
      obtain ⟨hb, he, hv⟩ := hm
      exact ⟨by simpa [ht] using hb, by simpa [ht] using he, hv.same_caches hf hg hn⟩
  · intro value hv
    exact (hi value hv).same_caches hf hg hn

theorem module.decode_element_section_loop.profile_complete
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (Rep (ElementEncodingFor profile)) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section_loop data env profile count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  induction entries generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, rfl, ⟨by cases env; rfl, by simp, by simp⟩⟩
    unfold module.decode_element_section_loop
    rw [loop]
    simp [module.decode_element_section_loop.body, hstop, he]
  | cons entry entries ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    obtain ⟨updated, current, hread, hraw, hadded⟩ := module.decode_element.complete
      data env profile pos middle entry hfirst (hv entry (by simp)) hrefs
    have hpost := module.decode_element.spec data pos env profile hrefs
    rw [hread] at hpost
    simp only [WP.spec_ok] at hpost
    obtain ⟨_, _, _, hbound, hprogress⟩ := hpost
    have hunchanged : updated.elements = env.elements := by rw [hadded.1]
    obtain ⟨elements, hpush, helements⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec updated.elements current (by rw [hunchanged]; scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by simp only [List.length_cons] at hc; scalar_tac))
    let after := { updated with elements := elements }
    obtain ⟨result, actual, hloop, hraws, htail⟩ := ih after middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by
        intro e he
        apply element_raw_valid_caches (hv e (by simp [he])) <;>
          dsimp only [after] <;> rw [hadded.1])
      (by simp only [after, helements, hunchanged, List.length_append, List.length_singleton]; omega)
      hbound
    refine ⟨result, current :: actual, ?_, ?_, ?_⟩
    · unfold module.decode_element_section_loop at hloop ⊢
      rw [loop]
      simpa [module.decode_element_section_loop.body, hmore, hread, hpush, hj, after,
        core.result.Result.Insts.CoreOpsTry.branch] using hloop
    · simp only [List.map_cons, hraw, hraws]
    · refine ⟨?_, ?_, ?_⟩
      · rw [htail.1]
        dsimp only [after]
        rw [hadded.1]
      · simpa only [after, helements, hunchanged, List.append_assoc, List.cons_append,
          List.nil_append] using htail.2.1
      · simpa only [after, hadded.2, List.flatMap_cons, List.append_assoc] using htail.2.2

theorem module.decode_element_section.profile_complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile) (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (VecEncoding (ElementEncodingFor profile)) data pos entries next)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section data pos env profile = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, actual, hr, hp⟩ := module.decode_element_section_loop.profile_complete
    data env profile count middle 0#u32 entries next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega) (by have := hcount.span; omega)
  refine ⟨result, actual, ?_, hp⟩
  simp [module.decode_element_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

theorem module.decode_element_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (Rep ElementEncoding) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section_loop data env .Wasm1 count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  exact module.decode_element_section_loop.profile_complete data env .Wasm1 count pos i entries next hb hc hv hsize hrefs

theorem module.decode_element_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (VecEncoding ElementEncoding) data pos entries next)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) (hrefs : env.declared_funcs.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section data pos env .Wasm1 = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  exact module.decode_element_section.profile_complete data pos env .Wasm1 entries next hb hv hsize hrefs

end Itasca
