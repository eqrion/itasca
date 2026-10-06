import Itasca.ModuleImportSection
import Itasca.ModuleGlobalSection

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

end Itasca.ModuleSections

namespace Itasca

open ModuleBinary ModuleSections

@[step]
theorem module.decode_element_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length)
    (hsize : env.elements.val.length ≤ start.val) :
    module.decode_element_section_loop data env count start 0#u32 ⦃ r => match r.1 with
      | .Ok next => ∃ added, added.length = count.val ∧ ElementsAdded env r.2 added ∧
          At (Rep ElementEncoding) data start (added.map ModuleEnv.rawElement) next ∧
          (∀ entry ∈ added, ElementValid env entry) ∧ r.2.elements.val.length ≤ next.val
      | .Err _ => True ⦄ := by
  unfold module.decode_element_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ ∃ added, added.length = s.2.2.val ∧
      ElementsAdded env s.1 added ∧
      At (Rep ElementEncoding) data start (added.map ModuleEnv.rawElement) s.2.1 ∧
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
        obtain ⟨idx, p1⟩ := pair
        have hs1 := hp.span
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
            obtain ⟨r, hi, hinit⟩ := WP.spec_imp_exists (module.decode_func_indices.spec data p2 current)
            cases r with
            | Err e => simp [hc, hi,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
              obtain ⟨init, next⟩ := pair
              obtain ⟨hib, hiv⟩ := hinit
              have hs3 := hib.span
              have hcapacity : current.elements.val.length < Usize.max := by scalar_tac
              simp [hc, hi]
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
                  hbytes.snoc (element_encoded hp hcb hib)
              · intro value hm
                rcases List.mem_append.mp hm with hm | hm
                · exact hvalid value hm
                · simpa [List.mem_singleton.mp hm] using hv
              · simp only [v_post, List.length_append, List.length_singleton]; omega
              · scalar_tac
  · exact ⟨by simp, [], by simp, ⟨by cases env; rfl, by simp⟩,
      ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩, by simp, hsize⟩

@[step]
theorem module.decode_element_section.spec (data : Slice U8) (pos : Usize) (env : module.Env)
    (hsize : env.elements.val.length ≤ pos.val) :
    module.decode_element_section data pos env ⦃ r => match r.1 with
      | .Ok next => ∃ added, ElementsAdded env r.2 added ∧
          At (VecEncoding ElementEncoding) data pos (added.map ModuleEnv.rawElement) next ∧
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
      (module.decode_element_section_loop.spec data env count start hs.2.2 (by omega))
    simp [module.decode_element_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok next =>
      obtain ⟨added, hlen, henv, hb, ht, hsize⟩ := hp
      exact ⟨added, henv, At.vector hc hb (by simpa using hlen), ht, hsize⟩

end Itasca
