import Itasca.Module.Readers.Copies
import Itasca.Module.Readers.Basic

open Aeneas Aeneas.Std

namespace Itasca

/-- Parameters precede the decoded locals; the explicit bound excludes the
allocation overflow possible in a caller-constructed oversized environment. -/
@[step]
theorem module.build_func_locals.spec (params declared : Slice types.ValueType)
    (hsize : params.val.length + declared.val.length ≤ Usize.max) :
    module.build_func_locals params declared ⦃ locals =>
      locals.val = params.val ++ declared.val ⦄ := by
  obtain ⟨out, hout, heq⟩ := WP.spec_imp_exists (module.copy_value_types.spec params)
  rw [module.build_func_locals, hout]
  simp only [bind_ok]
  simpa [module.build_func_locals_loop, module.copy_value_types_loop,
    module.build_func_locals_loop.body, module.copy_value_types_loop.body,
    List.drop_zero, heq] using
    module.copy_value_types_loop.spec declared out 0#usize (by simp) (by simpa [heq] using hsize)

@[step]
theorem module.push_locals_loop.spec (out : alloc.vec.Vec types.ValueType)
    (count : U32) (ty : types.ValueType) (i : U32)
    (hi : i.val ≤ count.val)
    (hsize : out.val.length + (count.val - i.val) ≤ Usize.max) :
    module.push_locals_loop out count ty i ⦃ result =>
      result.val = out.val ++ List.replicate (count.val - i.val) ty ⦄ := by
  unfold module.push_locals_loop
  apply loop.spec_decr_nat (fun p => count.val - p.2.val)
    (fun p => p.2.val ≤ count.val ∧
      p.1.val ++ List.replicate (count.val - p.2.val) ty =
        out.val ++ List.replicate (count.val - i.val) ty ∧
      p.1.val.length + (count.val - p.2.val) ≤ Usize.max)
  · rintro ⟨v, j⟩ ⟨hj, hv, hb⟩
    dsimp only at hj hv hb
    unfold module.push_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = count.val := by scalar_tac
      simp [heq] at hv
      simp [hv]
    · rename_i hmore
      have hlt : j.val < count.val := by scalar_tac
      have hcapacity : v.val.length < Usize.max := by omega
      step
      step
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try scalar_tac
      rw [out1_post, i1_post, ← hv]
      have hdiff : count.val - j.val = count.val - (j.val + 1) + 1 := by omega
      rw [hdiff, List.replicate_succ]
      simp [List.append_assoc]
  · exact ⟨hi, rfl, hsize⟩

@[step]
theorem module.push_locals.spec (out : alloc.vec.Vec types.ValueType)
    (count : U32) (ty : types.ValueType)
    (hsize : out.val.length + count.val ≤ Usize.max) :
    module.push_locals out count ty ⦃ result =>
      result.val = out.val ++ List.replicate count.val ty ⦄ := by
  simpa [module.push_locals] using
    module.push_locals_loop.spec out count ty 0#u32 (by simp) (by simpa using hsize)

namespace ModuleLocals

def declared (groups : List (U32 × types.ValueType)) : List types.ValueType :=
  groups.flatMap (fun (count, ty) => List.replicate count.val ty)

theorem at_snoc {data start pos next groups group}
    (hp : ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data start groups pos)
    (hg : ModuleBinary.At ModuleBinary.LocalEncoding data pos group next) :
    ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data start (groups ++ [group]) next := by
  obtain ⟨bs, hb, hs⟩ := hp
  obtain ⟨cs, hc, ht⟩ := hg
  exact ⟨bs ++ cs, hb.snoc hc, hs.append ht⟩

theorem local_at {data start pos next count ty}
    (hc : Leb128.Decoded data start count pos)
    (ht : ModuleBinary.At ModuleBinary.ValueTypeEncoding data pos ty next) :
    ModuleBinary.At ModuleBinary.LocalEncoding data start (count, ty) next := by
  obtain ⟨cs, hs, hl, hb, he⟩ := hc
  obtain ⟨ts, rfl, ht⟩ := ht
  exact ⟨cs ++ [ModuleBinary.valueByte ty], ⟨cs, he, rfl⟩, (⟨hs, hl, hb⟩ : Wasm.BytesAt data start cs pos).append ht⟩

end ModuleLocals

@[step]
theorem module.decode_locals_loop.spec (data : Slice U8) (groups : U32)
    (out : alloc.vec.Vec types.ValueType) (q : Usize) (i : U32)
    (hi : i.val ≤ groups.val) (hq : q.val ≤ data.length)
    (hsize : out.val.length ≤ limits.MAX_LOCALS.val) (profile : ValidationProfile := .Wasm1) :
    module.decode_locals_loop data profile groups out q i ⦃ r => match r with
      | .Ok (locals, next) => ∃ decoded,
          decoded.length = groups.val - i.val ∧
          ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data q decoded next ∧
          locals.val = out.val ++ ModuleLocals.declared decoded ∧
          locals.val.length ≤ limits.MAX_LOCALS.val ∧
          ∀ group ∈ decoded, ModuleBinary.ValueTypeAllowed profile group.2
      | .Err _ => True ⦄ := by
  unfold module.decode_locals_loop
  apply loop.spec_decr_nat (fun s => groups.val - s.2.2.val)
    (fun s => i.val ≤ s.2.2.val ∧ s.2.2.val ≤ groups.val ∧
      ∃ decoded, decoded.length = s.2.2.val - i.val ∧
        ModuleBinary.At (ModuleBinary.Rep ModuleBinary.LocalEncoding) data q decoded s.2.1 ∧
        s.1.val = out.val ++ ModuleLocals.declared decoded ∧
        s.1.val.length ≤ limits.MAX_LOCALS.val ∧
        ∀ group ∈ decoded, ModuleBinary.ValueTypeAllowed profile group.2)
  · rintro ⟨v, p, j⟩ ⟨hij, hj, decoded, hlen, hbytes, hvals, hcap, hallowed⟩
    dsimp only at hij hj hlen hbytes hvals hcap hallowed
    unfold module.decode_locals_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : j.val = groups.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨decoded, by omega, hbytes, hvals, hcap, hallowed⟩
    · rename_i hmore
      have hlt : j.val < groups.val := by scalar_tac
      obtain ⟨r, hr, hrpost⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p)
      rw [hr]
      cases r with
      | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
      | Ok pair =>
          obtain ⟨count, p1⟩ := pair
          obtain ⟨r, ht, htpost⟩ := WP.spec_imp_exists (module.decode_value_type.spec data p1 profile)
          simp [core.result.Result.Insts.CoreOpsTry.branch]
          rw [ht]
          cases r with
          | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
              obtain ⟨ty, p2⟩ := pair
              obtain ⟨bs, ⟨htype, hallowedType⟩, hspan⟩ := htpost
              have htpost : ModuleBinary.At ModuleBinary.ValueTypeEncoding data p1 ty p2 := ⟨bs, htype, hspan⟩
              have hlocal := ModuleLocals.local_at hrpost htpost
              simp only [bind_ok]
              step
              step
              split
              · simp
              · rename_i hroom
                have hcapacity : v.val.length + count.val ≤ Usize.max := by
                  have : limits.MAX_LOCALS.val < Usize.max := by
                    simp only [limits.MAX_LOCALS]
                    scalar_tac
                  scalar_tac
                step
                step
                refine ⟨?_, ?_, ⟨decoded ++ [(count, ty)], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
                · scalar_tac
                · scalar_tac
                · simp only [List.length_append, List.length_singleton]
                  scalar_tac
                · exact ModuleLocals.at_snoc hbytes hlocal
                · rw [out1_post, hvals]
                  simp [ModuleLocals.declared, List.flatMap_append, List.append_assoc]
                · simp only [out1_post, List.length_append, List.length_replicate]
                  scalar_tac
                · intro n value hm
                  rcases List.mem_append.mp hm with hm | hm
                  · exact hallowed (n, value) hm
                  · have he := List.mem_singleton.mp hm
                    cases he
                    exact hallowedType
                · scalar_tac
  · refine ⟨le_refl _, hi, [], by simp, ?_, by simp [ModuleLocals.declared], hsize, by simp⟩
    exact ⟨[], .nil, Wasm.BytesAt.nil data q hq⟩

@[step]
theorem module.decode_locals.spec (data : Slice U8) (pos : Usize) (profile : ValidationProfile := .Wasm1) :
    module.decode_locals data pos profile ⦃ r => match r with
      | .Ok (locals, next) => ∃ groups,
          ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.LocalEncoding) data pos groups next ∧
          locals.val = ModuleLocals.declared groups ∧
          locals.val.length ≤ limits.MAX_LOCALS.val ∧
          ∀ group ∈ groups, ModuleBinary.ValueTypeAllowed profile group.2
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
      simp [module.decode_locals, hr, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
      obtain ⟨groups, start⟩ := pair
      have hs := hp.span
      rw [module.decode_locals, hr]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      apply WP.spec_mono (module.decode_locals_loop.spec data groups (alloc.vec.Vec.new _) start 0#u32
        (by simp) hs.2.2 (by simp) profile)
      rintro r h
      cases r with
      | Err e => trivial
      | Ok pair =>
          obtain ⟨locals, next⟩ := pair
          obtain ⟨decoded, hn, hb, hv, hc, ha⟩ := h
          refine ⟨decoded, ?_, by simpa [alloc.vec.Vec.new] using hv, hc, fun n value hm => ha (n, value) hm⟩
          obtain ⟨count, hstart, hlength, hbound, he⟩ := hp
          obtain ⟨bytes, he', hs'⟩ := hb
          refine ⟨count ++ bytes, ⟨count, bytes, ?_, he', rfl⟩, ?_⟩
          · simpa using (hn ▸ he)
          · exact (⟨hstart, hlength, hbound⟩ : Wasm.BytesAt data pos count start).append hs'

end Itasca
