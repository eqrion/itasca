import Itasca.ModuleConstantsComplete
import Itasca.ModuleFramingComplete
import Itasca.ModuleData

open Aeneas Aeneas.Std

namespace Itasca

open ModuleBinary

theorem module.decode_data_segment.complete {data : Slice U8} {pos next : Usize}
    {env : module.Env} (segment : module.Data)
    (hb : At DataEncoding data pos (ModuleData.raw segment) next)
    (hv : ModuleData.Valid env segment) :
    module.decode_data_segment data pos env = .ok (.Ok (segment, next)) := by
  obtain ⟨bytes, ⟨memory, offset, init, hm, ho, hi, rfl⟩, hs⟩ := hb
  obtain ⟨afterOffset, hbefore, hinit⟩ := hs.split
  obtain ⟨afterMemory, hmemory, hoffset⟩ := hbefore.split
  have hvec : At ByteVecEncoding data afterOffset segment.init.val next := ⟨init, hi, hinit⟩
  obtain ⟨count, content, hn, hcount, encoded, hrep, hbytes⟩ := hvec.vector_split
  have hpayload : Wasm.BytesAt data content segment.init.val next := by simpa only [hrep.bytes] using hbytes
  have hrm := hmemory.read_u32 segment.memory_idx hm
  have hro := module.decode_const_expr.complete (env := env) ⟨offset, ho, hoffset⟩ hv.2
  have hrc := reader.read_u32_leb.complete data afterOffset count content hcount
  have hx : module.decode_data_segment data pos env ⦃ r => r = .Ok (segment, next) ⦄ := by
    simp [module.decode_data_segment, hrm, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hguard : ¬env.mem_types.val.length ≤ i.val := by have := hv.1; scalar_tac
    simp [hguard, hro, hrc, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have havail : content.val + n.val ≤ data.length := by
      have := hpayload.length
      have := hpayload.bound
      scalar_tac
    rw [module.have_bytes.complete data content n havail]
    simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hend : i2 = next := UScalar.eq_of_val_eq (by have := hpayload.length; scalar_tac)
    rw [hend, module.copy_bytes.complete data content next segment.init hpayload]
    cases segment
    simp [ModuleData.raw]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hx
  exact hr

theorem module.decode_data_section_loop.complete (data : Slice U8) (env : module.Env)
    (count : U32) (out : alloc.vec.Vec module.Data) (pos : Usize) (i : U32)
    (segments : List module.Data) (next : Usize)
    (hb : At (Rep DataEncoding) data pos (segments.map ModuleData.raw) next)
    (hc : i.val + segments.length = count.val) (hlen : out.val.length ≤ i.val)
    (hv : ∀ s ∈ segments, ModuleData.Valid env s) :
    ∃ result, module.decode_data_section_loop data env count out pos i = .ok (.Ok (result, next)) ∧
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
    have hread := module.decode_data_segment.complete segment hfirst (hv segment (by simp))
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

theorem module.decode_data_section.complete (data : Slice U8) (pos : Usize) (env : module.Env)
    (segments : alloc.vec.Vec module.Data) (next : Usize)
    (hb : At (VecEncoding DataEncoding) data pos (segments.val.map ModuleData.raw) next)
    (hv : ∀ s ∈ segments.val, ModuleData.Valid env s) :
    module.decode_data_section data pos env = .ok (.Ok (segments, next)) := by
  obtain ⟨count, first, hn, hc, hentries⟩ := hb.vector_split
  obtain ⟨result, hr, he⟩ := module.decode_data_section_loop.complete
    data env count (alloc.vec.Vec.new _) first 0#u32 segments.val next hentries
    (by simpa using hn.symm) (by simp) hv
  have heq : result = segments := alloc.vec.Vec.ext _ _ (by simpa using he)
  simp [module.decode_data_section, reader.read_u32_leb.complete data pos count first hc,
    hr, heq, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca
