import Itasca.Module.ModuleReaders
import Itasca.Module.ModuleConstants
import Itasca.Module.ModuleSegmentIndex

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

def raw (segment : module.Data) : ModuleBinary.Data :=
  ⟨segment.memory_idx, segment.offset, segment.init.val⟩

def Valid (env : module.Env) (segment : module.Data) : Prop :=
  segment.memory_idx.val < env.mem_types.val.length ∧
  ModuleConstants.Valid env segment.offset .I32

theorem at_snoc {R : ModuleBinary.Data → List U8 → Prop} {data start pos next values value}
    (h : ModuleBinary.At (ModuleBinary.Rep R) data start values pos)
    (h' : ModuleBinary.At R data pos value next) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

theorem encoded {data start p1 p2 p3 next memory offset count init}
    (hm : Leb128.Decoded data start memory p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hc : Leb128.Decoded data p2 count p3)
    (hi : Wasm.BytesAt data p3 init next) (hlen : init.length = count.val) :
    ModuleBinary.At ModuleBinary.DataEncoding data start
      ⟨memory, offset, init⟩ next := by
  obtain ⟨mb, hm, hs⟩ := ModuleBinary.At.of_u32 hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Wasm.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · refine ⟨mb, ob, cb ++ init, hm, ho, ?_, rfl⟩
    apply ModuleBinary.ByteVecEncoding.iff.mpr
    exact ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact (hs.append hos).append (hspan.append hi)

theorem profile_encoded {profile data start first p1 p2 p3 next flags memory explicit offset count init}
    (hf : Leb128.Decoded data start flags first)
    (hm : ModuleBinary.At (fun pair => ModuleBinary.SegmentIndexEncoding profile flags pair.1 pair.2)
      data first (memory, explicit) p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hc : Leb128.Decoded data p2 count p3)
    (hi : Wasm.BytesAt data p3 init next) (hlen : init.length = count.val) :
    ModuleBinary.At (ModuleBinary.DataEncodingFor profile) data start
      ⟨memory, offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨mb, hm, hms⟩ := hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Wasm.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨fb ++ mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · apply ModuleBinary.DataEncodingFor.of_parts hf hm ho
    exact ModuleBinary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact ((hfs.append hms).append hos).append (hspan.append hi)

end Itasca.ModuleData

namespace Itasca

/-- Data decoding proves both exact bytes and offset/index validity. -/
@[step]
theorem module.decode_data_segment.profile_spec (data : Slice U8) (pos : Usize) (env : module.Env) (profile : ValidationProfile) :
    module.decode_data_segment data pos env profile ⦃ r => match r with
      | .Ok (segment, next) =>
          ModuleBinary.At (ModuleBinary.DataEncodingFor profile) data pos (ModuleData.raw segment) next ∧
          ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [module.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨flags, first⟩
    change Leb128.Decoded data pos flags first at hm
    obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
      (module.decode_segment_index.profile_spec data first flags profile hm.span.2.2)
    cases r with
    | Err e =>
        simp [module.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok triple =>
        obtain ⟨memory, p1, explicit⟩ := triple
        simp [module.decode_data_segment, hr, hseg, core.result.Result.Insts.CoreOpsTry.branch]
        step
        split
        · simp
        · have hmem : memory.val < env.mem_types.val.length := by scalar_tac
          obtain ⟨r, hr, ho⟩ := WP.spec_imp_exists (module.decode_const_expr.spec data p1 env .I32)
          cases r with
          | Err e =>
            simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok pair =>
            rcases pair with ⟨offset, p2⟩
            change ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2 ∧
              ModuleConstants.Valid env offset .I32 at ho
            obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data p2)
            cases r with
            | Err e =>
              simp [hr, hlen, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                error.Error.Insts.CoreConvertFromOpError.from]
            | Ok pair =>
              rcases pair with ⟨count, p3⟩
              change Leb128.Decoded data p2 count p3 at hc
              simp [hr, hlen]
              step
              have hp3 : p3.val ≤ data.length := hc.span.2.2
              obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (module.have_bytes.spec data p3 n hp3)
              cases r with
              | Err e =>
                simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              | Ok u =>
                cases u
                simp only [hh, bind_ok]
                have havail' : p3.val + n.val ≤ data.length := havail.1.mp rfl
                step
                step
                refine ⟨ModuleData.profile_encoded hm hindex ho.1 hc init_post ?_, hmem, ho.2⟩
                have hl := init_post.length
                scalar_tac

@[step]
theorem module.decode_data_section_loop.profile_spec (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    module.decode_data_section_loop data env profile count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor profile))
            data start (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  unfold module.decode_data_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor profile))
        data start (s.1.val.map ModuleData.raw) s.2.1 ∧
      ∀ segment ∈ s.1.val, ModuleData.Valid env segment)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hbytes, hvalid⟩
    dsimp only at hi hlen hbytes hvalid
    unfold module.decode_data_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, hbytes, hvalid⟩
    · rename_i hmore
      have hlt : i.val < count.val := by scalar_tac
      have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (module.decode_data_segment.profile_spec data pos env profile)
      rw [hr]
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok pair =>
        rcases pair with ⟨segment, next⟩
        obtain ⟨hb, ht⟩ := hp
        simp [core.result.Result.Insts.CoreOpsTry.branch]
        step
        step
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · scalar_tac
        · simp only [out1_post, List.length_append, List.length_singleton]
          scalar_tac
        · simpa [out1_post, List.map_append] using ModuleData.at_snoc hbytes hb
        · intro entry he
          rw [out1_post] at he
          rcases List.mem_append.mp he with he | he
          · exact hvalid entry he
          · simpa [List.mem_singleton.mp he] using ht
        · scalar_tac
  · refine ⟨by simp, by simp, ?_, by simp [alloc.vec.Vec.new]⟩
    exact ⟨[], .nil, Wasm.BytesAt.nil data start hstart⟩

/-- The data count matches the list returned by the actual parser. -/
@[step]
theorem module.decode_data_section.profile_spec (data : Slice U8) (pos : Usize) (env : module.Env) (profile : ValidationProfile) :
    module.decode_data_section data pos env profile ⦃ r => match r with
      | .Ok (segments, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding (ModuleBinary.DataEncodingFor profile))
            data pos (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [module.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨count, start⟩
    change Leb128.Decoded data pos count start at hc
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (module.decode_data_section_loop.profile_spec data env profile count start hc.span.2.2)
    simp [module.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      rcases pair with ⟨segments, next⟩
      obtain ⟨hlen, hbytes, hvalid⟩ := hp
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
      have hcspan : Wasm.BytesAt data pos countBytes start := ⟨hcs, hcl, hcb⟩
      refine ⟨⟨countBytes ++ bytes, ?_, hcspan.append hs⟩, hvalid⟩
      exact ⟨countBytes, bytes, by simpa [hlen] using hce, he, rfl⟩

@[step]
theorem module.decode_data_segment.spec (data : Slice U8) (pos : Usize) (env : module.Env) :
    module.decode_data_segment data pos env .Wasm1 ⦃ r => match r with
      | .Ok (segment, next) =>
          ModuleBinary.At ModuleBinary.DataEncoding data pos (ModuleData.raw segment) next ∧
          ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  exact module.decode_data_segment.profile_spec data pos env .Wasm1

@[step]
theorem module.decode_data_section_loop.spec (data : Slice U8) (env : module.Env)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    module.decode_data_section_loop data env .Wasm1 count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          ModuleBinary.At (ModuleBinary.Rep ModuleBinary.DataEncoding)
            data start (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  exact module.decode_data_section_loop.profile_spec data env .Wasm1 count start hstart

@[step]
theorem module.decode_data_section.spec (data : Slice U8) (pos : Usize) (env : module.Env) :
    module.decode_data_section data pos env .Wasm1 ⦃ r => match r with
      | .Ok (segments, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding ModuleBinary.DataEncoding)
            data pos (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  exact module.decode_data_section.profile_spec data pos env .Wasm1

end Itasca
