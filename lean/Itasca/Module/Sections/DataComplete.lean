import Itasca.Module.Const.ParserComplete
import Itasca.Module.Readers.FramingComplete
import Itasca.Module.Sections.Data

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

private theorem data_active_parts {profile idx offset init bytes}
    (h : DataEncodingFor profile ⟨.Active idx offset, init⟩ bytes) :
    ∃ flags explicit fb mb ob ib, IndexEncoding flags fb ∧
      SegmentIndexEncoding profile flags idx explicit mb ∧ ConstEncoding offset ob ∧
      ByteVecEncoding init ib ∧ bytes = fb ++ mb ++ ob ++ ib := by
  cases profile with
  | Wasm1 =>
    obtain ⟨memory, off, mb, ob, ib, hm, hi, ho, hb, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := module.DataMode.Active.inj hm
    exact ⟨idx, false, mb, [], ob, ib, hi, ⟨rfl, rfl, rfl⟩, ho, hb, by simp⟩
  | Wasm2 =>
    cases h with
    | active hi ho hb =>
      obtain ⟨flags, fb, mb, hf, hm, rfl⟩ := hi.parts
      exact ⟨flags, _, fb, mb, _, _, hf, hm, ho, hb, rfl⟩

private theorem data_active_complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} (idx : U32) (offset : types.ConstExpr) (init : alloc.vec.Vec U8)
    (profile : ValidationProfile)
    (hb : At (DataEncodingFor profile) data pos ⟨.Active idx offset, init.val⟩ next)
    (hv : idx.val < env.mem_types.val.length ∧ ModuleConstants.Valid env offset .I32) :
    module.decode_data_segment data pos env profile = .ok (.Ok (⟨.Active idx offset, init⟩, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  obtain ⟨flags, explicit, flagBytes, memory, encodedOffset, encodedInit, hf, hm, ho, hi, rfl⟩ := data_active_parts he
  obtain ⟨afterOffset, hbefore, hinit⟩ := hs.split
  obtain ⟨afterMemory, hmemory, hoffset⟩ := hbefore.split
  have hvec : At ByteVecEncoding data afterOffset init.val next := ⟨encodedInit, hi, hinit⟩
  obtain ⟨count, content, hn, hcount, encoded, hrep, hbytes⟩ := hvec.vector_split
  have hpayload : Wasm.BytesAt data content init.val next := by simpa only [hrep.bytes] using hbytes
  obtain ⟨first, hflags, hindex⟩ := hmemory.split
  have hrf := hflags.read_u32 flags hf
  have hrm := module.decode_segment_index.profile_complete
    (show At (fun pair => SegmentIndexEncoding profile flags pair.1 pair.2)
      data first (idx, explicit) afterMemory from ⟨memory, hm, hindex⟩)
  have hro := module.decode_const_expr.complete (env := env) ⟨encodedOffset, ho, hoffset⟩ hv.2
    profile (hv.2.const_allowed (by cases profile <;> trivial))
  have hrc := reader.read_u32_leb.complete data afterOffset count content hcount
  have hx : module.decode_data_segment data pos env profile ⦃ r =>
      r = .Ok (⟨.Active idx offset, init⟩, next) ⦄ := by
    cases profile with
    | Wasm1 =>
      obtain ⟨rfl, rfl, rfl⟩ := hm
      have hpos := hindex.empty
      subst afterMemory
      simp [module.decode_data_segment, hrf, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have hguard : ¬env.mem_types.val.length ≤ i.val := by have := hv.1; scalar_tac
      simp [hguard, hro, hrc]
      step
      have havail : content.val + n.val ≤ data.length := by
        have := hpayload.length
        have := hpayload.bound
        scalar_tac
      rw [module.have_bytes.complete data content n havail]
      simp only [bind_ok]
      step
      have hend : i2 = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
      rw [hend, module.copy_bytes.complete data content next init hpayload]
      simp
    | Wasm2 =>
      have hpass : flags ≠ 1#u32 := by
        rcases hm with ⟨rfl, _, _, _⟩ | ⟨rfl, _, _⟩ <;> decide
      simp [module.decode_data_segment, hrf, hrm, hpass, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have hguard : ¬env.mem_types.val.length ≤ i.val := by have := hv.1; scalar_tac
      simp [hguard, hro, hrc]
      step
      have havail : content.val + n.val ≤ data.length := by
        have := hpayload.length
        have := hpayload.bound
        scalar_tac
      rw [module.have_bytes.complete data content n havail]
      simp only [bind_ok]
      step
      have hend : i2 = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
      rw [hend, module.copy_bytes.complete data content next init hpayload]
      simp
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

private theorem data_passive_complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} (init : alloc.vec.Vec U8)
    (hb : At (DataEncodingFor .Wasm2) data pos ⟨.Passive, init.val⟩ next) :
    module.decode_data_segment data pos env .Wasm2 = .ok (.Ok (⟨.Passive, init⟩, next)) := by
  obtain ⟨bytes, he, hs⟩ := hb
  cases he with
  | passive hf hi =>
    obtain ⟨first, hflags, hinit⟩ := hs.split
    have hvec : At ByteVecEncoding data first init.val next := ⟨_, hi, hinit⟩
    obtain ⟨count, content, hn, hcount, encoded, hrep, hbytes⟩ := hvec.vector_split
    have hpayload : Wasm.BytesAt data content init.val next := by simpa only [hrep.bytes] using hbytes
    have hrf := hflags.read_u32 1#u32 hf
    have hrc := reader.read_u32_leb.complete data first count content hcount
    have hx : module.decode_data_segment data pos env .Wasm2 ⦃ r =>
        r = .Ok (⟨.Passive, init⟩, next) ⦄ := by
      simp [module.decode_data_segment, hrf, hrc, core.result.Result.Insts.CoreOpsTry.branch]
      step
      have havail : content.val + n.val ≤ data.length := by
        have := hpayload.length
        have := hpayload.bound
        scalar_tac
      rw [module.have_bytes.complete data content n havail]
      simp only [bind_ok]
      step
      have hend : i = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
      rw [hend, module.copy_bytes.complete data content next init hpayload]
      simp
    obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
    exact hr

theorem module.decode_data_segment.profile_complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} (segment : module.Data) (profile : ValidationProfile)
    (hb : At (DataEncodingFor profile) data pos (ModuleData.raw segment) next)
    (hv : ModuleData.Valid env segment) :
    module.decode_data_segment data pos env profile = .ok (.Ok (segment, next)) := by
  obtain ⟨mode, init⟩ := segment
  cases mode with
  | Active idx offset => exact data_active_complete idx offset init profile hb hv
  | Passive =>
    cases profile with
    | Wasm2 => exact data_passive_complete init hb
    | Wasm1 =>
      obtain ⟨bytes, ⟨idx, offset, mb, ob, ib, he, _⟩, hs⟩ := hb
      cases he

theorem module.decode_data_section_loop.profile_complete (data : Slice U8) (env : module.Env) (profile : ValidationProfile)
    (count : U32) (out : alloc.vec.Vec module.Data) (pos : Usize) (i : U32)
    (segments : List module.Data) (next : Usize)
    (hb : At (Rep (DataEncodingFor profile)) data pos (segments.map ModuleData.raw) next)
    (hc : i.val + segments.length = count.val) (hlen : out.val.length ≤ i.val)
    (hv : ∀ s ∈ segments, ModuleData.Valid env s) :
    ∃ result, module.decode_data_section_loop data env profile count out pos i = .ok (.Ok (result, next)) ∧
      result.val = out.val ++ segments := by
  induction segments generalizing out pos i with
  | nil =>
    have he := hb.rep_nil
    have hstop : i ≥ count := by simp only [List.length_nil, Nat.add_zero] at hc; scalar_tac
    refine ⟨out, ?_, by simp⟩
    unfold module.decode_data_section_loop
    rw [loop]
    simp [module.decode_data_section_loop.body, hstop, he]
  | cons segment segments ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.rep_cons
    have hmore : ¬ i ≥ count := by simp only [List.length_cons] at hc; scalar_tac
    have hread := module.decode_data_segment.profile_complete segment profile hfirst (hv segment (by simp))
    obtain ⟨updated, hpush, hupdated⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.push_spec out segment (by simp only [List.length_cons] at hc; scalar_tac))
    obtain ⟨j, hj, hjval⟩ := WP.spec_imp_exists
      (U32.add_spec (x := i) (y := 1#u32) (by simp only [List.length_cons] at hc; scalar_tac))
    obtain ⟨result, hloop, hresult⟩ := ih updated middle j hrest
      (by simp only [List.length_cons] at hc; scalar_tac)
      (by simp only [hupdated, List.length_append, List.length_singleton]; scalar_tac)
      (by intro s hs; exact hv s (by simp [hs]))
    refine ⟨result, ?_, by simpa [hupdated, List.append_assoc] using hresult⟩
    unfold module.decode_data_section_loop
    rw [loop]
    simp [module.decode_data_section_loop.body, hmore, hread, hpush, hj,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact hloop

theorem module.decode_data_section.profile_complete (data : Slice U8) (pos : Usize) (env : module.Env) (profile : ValidationProfile)
    (segments : alloc.vec.Vec module.Data) (next : Usize)
    (hb : At (VecEncoding (DataEncodingFor profile)) data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s) :
    module.decode_data_section data pos env profile = .ok (.Ok (segments, next)) := by
  obtain ⟨count, first, hn, hc, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, he⟩ := module.decode_data_section_loop.profile_complete
    data env profile count (alloc.vec.Vec.new _) first 0#u32 segments.val next hentries
    (by simpa using hn.symm) (by simp) hv
  have heq : result = segments := alloc.vec.Vec.ext _ _ (by simpa using he)
  simp [module.decode_data_section, reader.read_u32_leb.complete data pos count first hc,
    hr, heq, core.result.Result.Insts.CoreOpsTry.branch]

theorem module.decode_data_segment.complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} (segment : module.Data)
    (hb : At DataEncoding data pos (ModuleData.raw segment) next)
    (hv : ModuleData.Valid env segment) :
    module.decode_data_segment data pos env .Wasm1 = .ok (.Ok (segment, next)) := by
  exact module.decode_data_segment.profile_complete segment .Wasm1 hb hv

theorem module.decode_data_section_loop.complete (data : Slice U8) (env : module.Env)
    (count : U32) (out : alloc.vec.Vec module.Data) (pos : Usize) (i : U32)
    (segments : List module.Data) (next : Usize)
    (hb : At (Rep DataEncoding) data pos (segments.map ModuleData.raw) next)
    (hc : i.val + segments.length = count.val) (hlen : out.val.length ≤ i.val)
    (hv : ∀ s ∈ segments, ModuleData.Valid env s) :
    ∃ result, module.decode_data_section_loop data env .Wasm1 count out pos i = .ok (.Ok (result, next)) ∧
      result.val = out.val ++ segments := by
  exact module.decode_data_section_loop.profile_complete data env .Wasm1 count out pos i segments next hb hc hlen hv

theorem module.decode_data_section.complete (data : Slice U8) (pos : Usize) (env : module.Env)
    (segments : alloc.vec.Vec module.Data) (next : Usize)
    (hb : At (VecEncoding DataEncoding) data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s) :
    module.decode_data_section data pos env .Wasm1 = .ok (.Ok (segments, next)) := by
  exact module.decode_data_section.profile_complete data pos env .Wasm1 segments next hb hv

end Itasca
