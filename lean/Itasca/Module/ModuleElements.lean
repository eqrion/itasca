import Itasca.Module.ModuleImportSection
import Itasca.Module.ModuleGlobalSection
import Itasca.Module.ModuleSegmentIndex

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_func_indices_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    module.decode_func_indices_loop data env count (alloc.vec.Vec.new _) start 0#u32 ⦃ r => match r with
      | .Ok (indices, next) => indices.val.length = count.val ∧
          At (Rep IndexEncoding) data start indices.val next ∧
          ∀ idx ∈ indices.val, idx.val < env.func_types.val.length
      | .Err _ => True ⦄ := by
  unfold module.decode_func_indices_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      At (Rep IndexEncoding) data start s.1.val s.2.1 ∧
      ∀ idx ∈ s.1.val, idx.val < env.func_types.val.length)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hbytes, hvalid⟩
    dsimp only at hi hlen hbytes hvalid
    unfold module.decode_func_indices_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, hbytes, hvalid⟩
    · rename_i hmore
      have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨idx, next⟩ := pair
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        split
        · simp
        · have hidx : idx.val < env.func_types.val.length := by scalar_tac
          step
          step
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · scalar_tac
          · simp only [out1_post, List.length_append, List.length_singleton]; scalar_tac
          · simpa only [out1_post] using hbytes.snoc (At.of_u32 hp)
          · intro value hm
            rw [out1_post] at hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hvalid value hm
            · simpa [List.mem_singleton.mp hm] using hidx
          · scalar_tac
  · exact ⟨by simp, by simp, ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, by simp⟩

@[step]
theorem module.decode_func_indices.spec (data : Slice U8) (pos : Usize) (env : module.Env) :
    module.decode_func_indices data pos env ⦃ r => match r with
      | .Ok (indices, next) => At (VecEncoding IndexEncoding) data pos indices.val next ∧
          ∀ idx ∈ indices.val, idx.val < env.func_types.val.length
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_func_indices, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_func_indices_loop.spec data env count start hc.span.2.2)
    simp [module.decode_func_indices, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      obtain ⟨indices, next⟩ := pair
      obtain ⟨hlen, hb, ht⟩ := hp
      exact ⟨At.vector hc hb hlen, ht⟩

end Itasca

namespace Itasca.ModuleSections

def ElementsAdded (env result : module.Env) (added : List module.Element) : Prop :=
  result = { env with elements := result.elements } ∧ result.elements.val = env.elements.val ++ added

def ElementValid (env : module.Env) (entry : module.Element) : Prop :=
  entry.table_idx.val < env.table_types.val.length ∧ ModuleConstants.Valid env entry.offset .I32 ∧
    ∀ idx ∈ entry.init.val, idx.val < env.func_types.val.length

theorem element_encoded {data start p1 p2 next tableIdx offset init}
    (ht : Leb128.Decoded data start tableIdx p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hi : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.IndexEncoding) data p2 init next) :
    ModuleBinary.At ModuleBinary.ElementEncoding data start ⟨tableIdx, offset, init⟩ next := by
  obtain ⟨tb, ht, hs⟩ := ModuleBinary.At.of_u32 ht
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨ib, hi, his⟩ := hi
  exact ⟨tb ++ ob ++ ib, ⟨tb, ob, ib, ht, ho, hi, rfl⟩, (hs.append hos).append his⟩

theorem element_profile_encoded {profile data start first p1 p2 p3 next flags tableIdx explicit offset init}
    (hf : Leb128.Decoded data start flags first)
    (ht : ModuleBinary.At (fun pair => ModuleBinary.SegmentIndexEncoding profile flags pair.1 pair.2)
      data first (tableIdx, explicit) p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hk : ModuleBinary.At (fun (_ : Unit) => ModuleBinary.ElementKindEncoding explicit) data p2 () p3)
    (hi : ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.IndexEncoding) data p3 init next) :
    ModuleBinary.At (ModuleBinary.ElementEncodingFor profile) data start ⟨tableIdx, offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨tb, ht, hts⟩ := ht
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨kb, hk, hks⟩ := hk
  obtain ⟨ib, hi, his⟩ := hi
  exact ⟨fb ++ tb ++ ob ++ kb ++ ib, ModuleBinary.ElementEncodingFor.of_parts hf ht ho hk hi,
    (((hfs.append hts).append hos).append hks).append his⟩

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_element_section_loop.profile_spec (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) :
    module.decode_element_section_loop data env profile count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep (ElementEncodingFor profile)) data start (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep (ElementEncodingFor profile)) data start (added.map ModuleEnv.rawElement) s.2.1 ∧
      (∀ entry ∈ added, ElementValid env entry) ∧ s.1.elements.val.length ≤ s.2.1.val)
  · rintro ⟨current, pos, i⟩ ⟨hi, added, hlen, henv, hbytes, hvalid, hsize⟩
    dsimp only at hi hlen henv hbytes hvalid hsize
    unfold module.decode_element_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨added, by omega, henv, hbytes, hvalid, hsize⟩
    · rename_i hmore
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
      rw [hr]
      cases r with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
        obtain ⟨flags, first⟩ := pair
        obtain ⟨r, hseg, hprefix⟩ := WP.spec_imp_exists
          (module.decode_segment_index.profile_spec data first flags profile hp.span.2.2)
        simp [core.result.Result.Insts.CoreOpsTry.branch, hseg]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok triple =>
            obtain ⟨idx, p1, explicit⟩ := triple
            have hs0 := hp.span
            have hs1 := hprefix.span
            simp [core.result.Result.Insts.CoreOpsTry.branch]
            step
            split
            · simp
            · have hidx : idx.val < env.table_types.val.length := by
                have ht : current.table_types = env.table_types := by rw [henv.1]
                scalar_tac
              obtain ⟨r, hc, hconst⟩ := WP.spec_imp_exists (module.decode_const_expr.spec data p1 current .I32)
              cases r with
              | Err e => simp [hc,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok pair =>
                obtain ⟨offset, p2⟩ := pair
                obtain ⟨hcb, hcv⟩ := hconst
                have hs2 := hcb.span
                simp [hc, core.result.Result.Insts.CoreOpsTry.branch]
                cases explicit with
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    have hkindBytes : At (fun (_ : Unit) => ElementKindEncoding false) data p2 () p2 :=
                      ⟨[], rfl, Wasm.BytesAt.nil data p2 hs2.2⟩
                    obtain ⟨r, hi, hinit⟩ := WP.spec_imp_exists (module.decode_func_indices.spec data p2 current)
                    cases r with
                    | Err e => simp [hi,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                    | Ok pair =>
                      obtain ⟨init, next⟩ := pair
                      obtain ⟨hib, hiv⟩ := hinit
                      have hs3 := hib.span
                      have hcapacity : current.elements.val.length < Usize.max := by scalar_tac
                      simp [hi]
                      step
                      step
                      let entry : module.Element := ⟨idx, offset, init⟩
                      have hglobal : current.global_types = env.global_types := by rw [henv.1]
                      have hfunc : current.func_types = env.func_types := by rw [henv.1]
                      have hv : ElementValid env entry := ⟨hidx,
                        hcv.append_globals [] (by simp [hglobal]) (by rw [henv.1]),
                        by simpa only [hfunc] using hiv⟩
                      refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                      · scalar_tac
                      · simp only [List.length_append, List.length_singleton]; scalar_tac
                      · constructor
                        · rw [henv.1]
                        · simp only [v_post, henv.2, List.append_assoc, entry]
                      · simpa only [List.map_append, List.map_cons, List.map_nil, ModuleEnv.rawElement, entry] using
                          hbytes.snoc (element_profile_encoded hp hprefix hcb hkindBytes hib)
                      · intro value hm
                        rcases List.mem_append.mp hm with hm | hm
                        · exact hvalid value hm
                        · simpa [List.mem_singleton.mp hm] using hv
                      · simp only [v_post, List.length_append, List.length_singleton]; omega
                      · scalar_tac
                | true =>
                    simp only [↓reduceIte]
                    obtain ⟨r, hkind, hkindRead⟩ := WP.spec_imp_exists (reader.read_byte.module_spec data p2)
                    simp [hkind]
                    cases r with
                    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
                        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                        error.Error.Insts.CoreConvertFromOpError.from]
                    | Ok kindPair =>
                        obtain ⟨kind, kindPos⟩ := kindPair
                        by_cases hzero : kind = 0#u8
                        · have hkindBytes : At (fun (_ : Unit) => ElementKindEncoding true) data p2 () kindPos :=
                            ⟨[0#u8], rfl, by simpa [hzero] using At.byte hkindRead⟩
                          have hkindSpan := hkindBytes.span
                          simp [core.result.Result.Insts.CoreOpsTry.branch, hzero]
                          obtain ⟨r, hi, hinit⟩ := WP.spec_imp_exists (module.decode_func_indices.spec data kindPos current)
                          cases r with
                          | Err e => simp [hi,
                              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                          | Ok pair =>
                            obtain ⟨init, next⟩ := pair
                            obtain ⟨hib, hiv⟩ := hinit
                            have hs3 := hib.span
                            have hcapacity : current.elements.val.length < Usize.max := by scalar_tac
                            simp [hi]
                            step
                            step
                            let entry : module.Element := ⟨idx, offset, init⟩
                            have hglobal : current.global_types = env.global_types := by rw [henv.1]
                            have hfunc : current.func_types = env.func_types := by rw [henv.1]
                            have hv : ElementValid env entry := ⟨hidx,
                              hcv.append_globals [] (by simp [hglobal]) (by rw [henv.1]),
                              by simpa only [hfunc] using hiv⟩
                            refine ⟨?_, ⟨added ++ [entry], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                            · scalar_tac
                            · simp only [List.length_append, List.length_singleton]; scalar_tac
                            · constructor
                              · rw [henv.1]
                              · simp only [v_post, henv.2, List.append_assoc, entry]
                            · simpa only [List.map_append, List.map_cons, List.map_nil, ModuleEnv.rawElement, entry] using
                                hbytes.snoc (element_profile_encoded hp hprefix hcb hkindBytes hib)
                            · intro value hm
                              rcases List.mem_append.mp hm with hm | hm
                              · exact hvalid value hm
                              · simpa [List.mem_singleton.mp hm] using hv
                            · simp only [v_post, List.length_append, List.length_singleton]; omega
                            · scalar_tac
                        · have hn : kind.val ≠ 0 := fun h => hzero (UScalar.eq_of_val_eq h)
                          simp [core.result.Result.Insts.CoreOpsTry.branch, hn]

  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, by simp, hsize⟩

@[step]
theorem module.decode_element_section.profile_spec (data : Slice U8) (pos : Usize) (env : module.Env) (profile : ValidationProfile)
    (hsize : env.elements.val.length ≤ pos.val) :
    module.decode_element_section data pos env profile ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding (ElementEncodingFor profile)) data pos (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e => simp [module.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    obtain ⟨count, start⟩ := pair
    have hs := hc.span
    obtain ⟨⟨r, result⟩, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_element_section_loop.profile_spec data env profile count start hs.2.2 (by omega))
    simp [module.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize⟩

@[step]
theorem module.decode_element_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) :
    module.decode_element_section_loop data env .Wasm1 count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep ElementEncoding) data start (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  exact module.decode_element_section_loop.profile_spec data env .Wasm1 count start hstart hsize

@[step]
theorem module.decode_element_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hsize : env.elements.val.length ≤ pos.val) :
    module.decode_element_section data pos env .Wasm1 ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding ElementEncoding) data pos (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  exact module.decode_element_section.profile_spec data pos env .Wasm1 hsize

end Itasca
