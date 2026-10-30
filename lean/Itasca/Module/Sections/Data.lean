import Itasca.Module.Elab.SegmentSyntax
import Itasca.Module.Readers.Basic
import Itasca.Module.Const.Parser
import Itasca.Module.Readers.SegmentIndex

/-!
# Data section parser

Soundness of `metadata.decode_data_segment`, `metadata.decode_data_section_loop` and
`metadata.decode_data_section`. Accepted segments are spans of the independent grammar
(`DataEncodingFor` for the profile, `DataEncoding` for Wasm 1.0) and satisfy `ModuleData.Valid`,
which covers the memory index and the offset initializer of active segments. Passive segments
need Wasm 2.0. Completeness is in `Module/Sections/DataComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca.ModuleData

/-- A repetition span extends by one segment at its end. -/
theorem at_snoc {R : ModuleBinary.Data → List U8 → Prop} {data start pos next values value}
    (h : ModuleBinary.At (ModuleBinary.Rep R) data start values pos)
    (h' : ModuleBinary.At R data pos value next) :
    ModuleBinary.At (ModuleBinary.Rep R) data start (values ++ [value]) next := by
  obtain ⟨bytes, hr, hs⟩ := h
  obtain ⟨last, he, ht⟩ := h'
  exact ⟨bytes ++ last, hr.snoc he, hs.append ht⟩

/-- Like `encoded` for a profile: a flag word and the profile's index encoding give an active
`DataEncodingFor profile`. -/
theorem profile_encoded {profile data start first p1 p2 p3 next flags memory explicit offset count init}
    (hf : Leb128.Decoded data start flags first)
    (hm : ModuleBinary.At (fun pair => ModuleBinary.SegmentIndexEncoding profile flags pair.1 pair.2)
      data first (memory, explicit) p1)
    (ho : ModuleBinary.At ModuleBinary.ConstEncoding data p1 offset p2)
    (hc : Leb128.Decoded data p2 count p3)
    (hi : Wasm1.BytesAt data p3 init next) (hlen : init.length = count.val) :
    ModuleBinary.At (ModuleBinary.DataEncodingFor profile) data start
      ⟨.Active memory offset, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨mb, hm, hms⟩ := hm
  obtain ⟨ob, ho, hos⟩ := ho
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hspan : Wasm1.BytesAt data p2 cb p3 := ⟨hcs, hcl, hcb⟩
  refine ⟨fb ++ mb ++ ob ++ (cb ++ init), ?_, ?_⟩
  · apply ModuleBinary.DataEncodingFor.of_parts hf hm ho
    exact ModuleBinary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩
  · exact ((hfs.append hms).append hos).append (hspan.append hi)

/-- Flag `1` followed by a counted byte string is a passive Wasm 2.0 data segment. -/
theorem passive_encoded {data start first content next count init}
    (hf : Leb128.Decoded data start 1#u32 first)
    (hc : Leb128.Decoded data first count content)
    (hi : Wasm1.BytesAt data content init next) (hlen : init.length = count.val) :
    ModuleBinary.At (ModuleBinary.DataEncodingFor .Wasm2) data start ⟨.Passive, init⟩ next := by
  obtain ⟨fb, hf, hfs⟩ := ModuleBinary.At.of_u32 hf
  obtain ⟨cb, hcs, hcl, hcb, hc⟩ := hc
  have hcount : Wasm1.BytesAt data first cb content := ⟨hcs, hcl, hcb⟩
  exact ⟨fb ++ (cb ++ init), .passive hf
    (ModuleBinary.ByteVecEncoding.iff.mpr ⟨cb, by simpa [hlen] using hc, rfl⟩),
    hfs.append (hcount.append hi)⟩

end Itasca.ModuleData

namespace Itasca

/-- An accepted `metadata.decode_data_segment` is a `DataEncodingFor profile` span and its segment
is `ModuleData.Valid`. -/
@[step]
theorem metadata.decode_data_segment.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env) (profile : ValidationProfile) :
    metadata.decode_data_segment data pos env profile ⦃ r => match r with
      | .Ok (segment, next) =>
          ModuleBinary.At (ModuleBinary.DataEncodingFor profile) data pos (ModuleData.raw segment) next ∧
          ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hm⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨flags, first⟩
    change Leb128.Decoded data pos flags first at hm
    cases profile with
    | Wasm1 =>
      obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
        (metadata.decode_segment_index.profile_spec data first flags ValidationProfile.Wasm1 hm.span.2.2)
      cases r with
      | Err e => simp [metadata.decode_segment_index] at hseg
      | Ok triple =>
          obtain ⟨memory, p1, explicit⟩ := triple
          simp only [metadata.decode_segment_index, Result.ok.injEq, core.result.Result.Ok.injEq,
            Prod.mk.injEq] at hseg
          rcases hseg with ⟨rfl, rfl, rfl⟩
          simp [metadata.decode_data_segment, hr, core.result.Result.Insts.CoreOpsTry.branch]
          step
          split
          · simp
          · have hmem : flags.val < env.mem_types.val.length := by scalar_tac
            obtain ⟨r, hr, ho⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data first env .I32 ValidationProfile.Wasm1)
            cases r with
            | Err e =>
              simp [hr, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
            | Ok pair =>
              rcases pair with ⟨offset, p2⟩
              change ModuleBinary.At ModuleBinary.ConstEncoding data first offset p2 ∧
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
                obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data p3 n hp3)
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
    | Wasm2 =>
      by_cases hpass : flags = 1#u32
      · subst flags
        obtain ⟨r, hlen, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data first)
        cases r with
        | Err e => simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            error.Error.Insts.CoreConvertFromOpError.from]
        | Ok pair =>
          obtain ⟨count, content⟩ := pair
          simp [metadata.decode_data_segment, hr, hlen, core.result.Result.Insts.CoreOpsTry.branch]
          step
          have hcontent : content.val ≤ data.length := hc.span.2.2
          obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data content n hcontent)
          cases r with
          | Err e => simp [hh, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok u =>
            cases u
            simp only [hh, bind_ok]
            have havail' : content.val + n.val ≤ data.length := havail.1.mp rfl
            step
            step
            refine ⟨ModuleData.passive_encoded hm hc init_post ?_, trivial⟩
            have hl := init_post.length
            scalar_tac
      ·
        obtain ⟨r, hseg, hindex⟩ := WP.spec_imp_exists
          (metadata.decode_segment_index.profile_spec data first flags ValidationProfile.Wasm2 hm.span.2.2)
        cases r with
        | Err e =>
            simp [metadata.decode_data_segment, hr, hpass, hseg, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok triple =>
            obtain ⟨memory, p1, explicit⟩ := triple
            simp [metadata.decode_data_segment, hr, hpass, hseg, core.result.Result.Insts.CoreOpsTry.branch]
            step
            split
            · simp
            · have hmem : memory.val < env.mem_types.val.length := by scalar_tac
              obtain ⟨r, hr, ho⟩ := WP.spec_imp_exists (metadata.decode_const_expr.spec data p1 env .I32 ValidationProfile.Wasm2)
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
                  obtain ⟨r, hh, havail⟩ := WP.spec_imp_exists (metadata.have_bytes.spec data p3 n hp3)
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

/-- The data loop returns `count` segments forming a `Rep` span, all valid. -/
@[step]
theorem metadata.decode_data_section_loop.profile_spec (data : Slice U8) (env : metadata.Env) (profile : ValidationProfile)
    (count : U32) (start : Usize) (hstart : start.val ≤ data.length) :
    metadata.decode_data_section_loop data env profile count (alloc.vec.Vec.new _) start 0#u32 ⦃ r =>
      match r with
      | .Ok (segments, next) => segments.val.length = count.val ∧
          ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor profile))
            data start (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  unfold metadata.decode_data_section_loop
  apply loop.spec_decr_nat (fun s => count.val - s.2.2.val)
    (fun s => s.2.2.val ≤ count.val ∧ s.1.val.length = s.2.2.val ∧
      ModuleBinary.At (ModuleBinary.Rep (ModuleBinary.DataEncodingFor profile))
        data start (s.1.val.map ModuleData.raw) s.2.1 ∧
      ∀ segment ∈ s.1.val, ModuleData.Valid env segment)
  · rintro ⟨out, pos, i⟩ ⟨hi, hlen, hbytes, hvalid⟩
    dsimp only at hi hlen hbytes hvalid
    unfold metadata.decode_data_section_loop.body
    dsimp only
    split
    · rename_i hstop
      have heq : i.val = count.val := by scalar_tac
      exact ⟨by omega, hbytes, hvalid⟩
    · rename_i hmore
      have hlt : i.val < count.val := by scalar_tac
      have hcapacity : out.val.length < Usize.max := by scalar_tac
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (metadata.decode_data_segment.profile_spec data pos env profile)
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
    exact ⟨[], .nil, Wasm1.BytesAt.nil data start hstart⟩

/-- An accepted `metadata.decode_data_section` returns segments forming a `VecEncoding` span, all
valid. -/
@[step]
theorem metadata.decode_data_section.profile_spec (data : Slice U8) (pos : Usize) (env : metadata.Env) (profile : ValidationProfile) :
    metadata.decode_data_section data pos env profile ⦃ r => match r with
      | .Ok (segments, next) =>
          ModuleBinary.At (ModuleBinary.VecEncoding (ModuleBinary.DataEncodingFor profile))
            data pos (segments.val.map ModuleData.raw) next ∧
          ∀ segment ∈ segments.val, ModuleData.Valid env segment
      | .Err _ => True ⦄ := by
  obtain ⟨r, hr, hc⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data pos)
  cases r with
  | Err e =>
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  | Ok pair =>
    rcases pair with ⟨count, start⟩
    change Leb128.Decoded data pos count start at hc
    obtain ⟨r, hloop, hp⟩ := WP.spec_imp_exists
      (metadata.decode_data_section_loop.profile_spec data env profile count start hc.span.2.2)
    simp [metadata.decode_data_section, hr, core.result.Result.Insts.CoreOpsTry.branch]
    rw [hloop]
    cases r with
    | Err e => simp
    | Ok pair =>
      rcases pair with ⟨segments, next⟩
      obtain ⟨hlen, hbytes, hvalid⟩ := hp
      obtain ⟨bytes, he, hs⟩ := hbytes
      obtain ⟨countBytes, hcs, hcl, hcb, hce⟩ := hc
      have hcspan : Wasm1.BytesAt data pos countBytes start := ⟨hcs, hcl, hcb⟩
      refine ⟨⟨countBytes ++ bytes, ?_, hcspan.append hs⟩, hvalid⟩
      exact ⟨countBytes, bytes, by simpa [hlen] using hce, he, rfl⟩

end Itasca
