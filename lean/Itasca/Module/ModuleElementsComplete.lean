import Itasca.Module.ModuleEnvRequirements
import Itasca.Module.ModuleElements
import Itasca.Module.ModuleReadersComplete
import Itasca.Module.ModuleConstantsComplete

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


theorem module.decode_element_section_loop.profile_complete
    (data : Slice U8) (env : module.Env) (profile : ValidationProfile) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (Rep (ElementEncodingFor profile)) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section_loop data env profile count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  induction entries generalizing env pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨env, [], ?_, rfl, by exact ⟨by cases env; rfl, by simp⟩⟩
    unfold module.decode_element_section_loop
    rw [loop]
    simp [module.decode_element_section_loop.body, hstop, he]
  | cons entry entries ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    obtain ⟨bs, he, hs⟩ := hfirst
    obtain ⟨flags, explicit, flagBytes, tableBytes, offsetBytes, kindBytes, initBytes,
      hf, ht, ho, hk, hi, rfl⟩ := he.parts
    obtain ⟨kindPos, hbeforeKind, hinit⟩ := hs.split
    obtain ⟨p2, hbeforeOffset, hkind⟩ := hbeforeKind.split
    obtain ⟨p1, hbeforeIndex, hoffset⟩ := hbeforeOffset.split
    obtain ⟨first, hflags, htable⟩ := hbeforeIndex.split
    have hflagsAt : At IndexEncoding data pos flags first := ⟨_, hf, hflags⟩
    have hindexAt : At (fun pair => SegmentIndexEncoding profile flags pair.1 pair.2)
        data first (entry.tableIdx, explicit) p1 := ⟨_, ht, htable⟩
    have hreadindex := module.decode_segment_index.profile_complete hindexAt
    have hprogress := hflagsAt.index_decoded.span
    have hindexSpan := hindexAt.span
    have hkindSpan := hkind.length
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    obtain ⟨htvalid, hovalid, hivalid⟩ := hv entry (by simp)
    have hntable : ¬ env.table_types.val.length ≤ entry.tableIdx.val := Nat.not_le.mpr htvalid
    have hvalid : ¬ UScalar.cast .Usize entry.tableIdx ≥ alloc.vec.Vec.len env.table_types := by scalar_tac
    have hreadexpr := module.decode_const_expr.complete (show At ConstEncoding data p1 entry.offset p2 from ⟨_, ho, hoffset⟩) hovalid
    obtain ⟨init, hreadinit, hinitval⟩ := module.decode_func_indices.complete data kindPos env entry.init middle ⟨_, hi, hinit⟩ hivalid
    have hbound := hinit.bound
    let current : module.Element := ⟨entry.tableIdx, entry.offset, init⟩
    obtain ⟨elements, hpush, helements⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec env.elements current (by scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by scalar_tac))
    let updated := {env with elements := elements}
    obtain ⟨result, actual, hloop, hraw, hadded⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by
        intro e he
        obtain ⟨ht, ho, hi⟩ := hv e (by simp [he])
        exact ⟨ht, ho.append_globals [] (by simp [updated]) rfl, hi⟩)
      (by simp only [updated, helements, List.length_append, List.length_singleton];
          have := hoffset.length; have := hinit.length; omega)
    refine ⟨result, current :: actual, ?_, ?_, ?_⟩
    · unfold module.decode_element_section_loop at hloop ⊢
      rw [loop]
      cases explicit with
      | false =>
          have hkempty : kindBytes = [] := hk
          subst kindBytes
          obtain rfl := hkind.empty
          simpa [module.decode_element_section_loop.body, hmore, hflagsAt.read_index, hreadindex,
            hntable, hreadexpr, hreadinit, hpush, hj, current,
            core.result.Result.Insts.CoreOpsTry.branch, lift] using hloop
      | true =>
          have hkkind : kindBytes = [0#u8] := hk
          subst kindBytes
          simpa [module.decode_element_section_loop.body, hmore, hflagsAt.read_index, hreadindex,
            hntable, hreadexpr, hkind.read_byte, hreadinit, hpush, hj, current,
            core.result.Result.Insts.CoreOpsTry.branch, lift] using hloop

    · simp only [List.map_cons, hraw]
      congr 1
      cases entry
      simp_all [ModuleEnv.rawElement, current]
    · refine ⟨?_, ?_⟩
      · rw [hadded.1]
      · simpa [updated, helements, List.append_assoc] using hadded.2

theorem module.decode_element_section.profile_complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (profile : ValidationProfile) (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (VecEncoding (ElementEncodingFor profile)) data pos entries next)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section data pos env profile = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  obtain ⟨count, middle, hc, hcount, hentries⟩ := hb.vector_split
  obtain ⟨result, actual, hr, hp⟩ := module.decode_element_section_loop.profile_complete
    data env profile count middle 0#u32 entries next hentries (by simpa using hc.symm) hv
    (by have := hcount.span; omega)
  refine ⟨result, actual, ?_, hp⟩
  simp [module.decode_element_section, reader.read_u32_leb.complete data pos count middle hcount,
    core.result.Result.Insts.CoreOpsTry.branch, hr]

theorem module.decode_element_section_loop.complete
    (data : Slice U8) (env : module.Env) (count : U32) (pos : Usize) (i : U32)
    (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (Rep ElementEncoding) data pos entries next)
    (hc : i.val + entries.length = count.val)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section_loop data env .Wasm1 count pos i = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  exact module.decode_element_section_loop.profile_complete data env .Wasm1 count pos i entries next hb hc hv hsize

theorem module.decode_element_section.complete (data : Slice U8) (pos : Usize)
    (env : module.Env) (entries : List ModuleBinary.Element) (next : Usize)
    (hb : At (VecEncoding ElementEncoding) data pos entries next)
    (hv : ∀ entry ∈ entries, ElementValidRaw env entry)
    (hsize : env.elements.val.length ≤ pos.val) :
    ∃ result actual, module.decode_element_section data pos env .Wasm1 = .ok (.Ok next, result) ∧
      actual.map ModuleEnv.rawElement = entries ∧ ElementsAdded env result actual := by
  exact module.decode_element_section.profile_complete data pos env .Wasm1 entries next hb hv hsize

end Itasca
