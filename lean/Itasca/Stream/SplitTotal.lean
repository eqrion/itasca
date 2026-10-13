import Itasca.Stream.Source

open Aeneas Aeneas.Std

namespace Itasca

/-- The splitter is total before the module-size guard, including short and
malformed buffers. Its output always describes three adjacent in-bounds regions. -/
theorem stream.find_code_region_loop.spec (bytes : Slice U8) (pos : Usize) :
    stream.find_code_region_loop bytes (Slice.len bytes) pos ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  unfold stream.find_code_region_loop
  apply loop.spec_decr_nat (fun pos => bytes.length - pos.val) (fun _ => True)
  · intro cursor _
    unfold stream.find_code_region_loop.body
    split
    · simp
    · rename_i hcursor
      have hcursor' : cursor.val < bytes.length := by scalar_tac
      step
      split
      · split
        · simp; scalar_tac
        · step
          obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
          rw [hr]
          cases r with
          | Err e =>
            simp only [bind_ok]
            split <;> simp_all
          | Ok p =>
            obtain ⟨size, contents⟩ := p
            obtain ⟨_, _, hd⟩ := hp
            have hprogress := hd.span.1
            have hbound := hd.span.2.2
            simp only [bind_ok]
            step*
            scalar_tac
      · step
        obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_len.spec bytes i)
        rw [hr]
        cases r with
        | Err e =>
          simp only [bind_ok]
          split <;> simp_all
          scalar_tac
        | Ok p =>
          obtain ⟨size, contents⟩ := p
          obtain ⟨_, _, hd⟩ := hp
          have hprogress := hd.span.1
          have hbound := hd.span.2.2
          simp only [bind_ok]
          step* <;> scalar_tac
  · trivial

@[step]
theorem stream.find_code_region.spec (bytes : Slice U8) :
    stream.find_code_region bytes ⦃ result =>
      result.1.val ≤ result.2.val ∧ result.2.val ≤ bytes.length ⦄ := by
  simpa [stream.find_code_region] using
    stream.find_code_region_loop.spec bytes 8#usize

theorem stream.find_code_region.total (bytes : Slice U8) :
    ∃ result, stream.find_code_region bytes = .ok result := by
  obtain ⟨result, hr, _⟩ := WP.spec_imp_exists (stream.find_code_region.spec bytes)
  exact ⟨result, hr⟩

theorem stream.find_code_region.bounds (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    first.val ≤ last.val ∧ last.val ≤ bytes.length := by
  have hs := stream.find_code_region.spec bytes
  simpa [h] using hs

/-- Actual slice operations at the split boundaries are safe and reconstruct
all input bytes, regardless of whether the input is a valid module. -/
theorem stream.find_code_region.slices (bytes : Slice U8) (first last : Usize)
    (h : stream.find_code_region bytes = .ok (first, last)) :
    ∃ environment code tail : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨0#usize, first⟩ = .ok environment ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨first, last⟩ = .ok code ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨last, Slice.len bytes⟩ = .ok tail ∧
      bytes.val = environment.val ++ code.val ++ tail.val := by
  obtain ⟨hfirst, hlast⟩ := stream.find_code_region.bounds bytes first last h
  have slice_spec (start finish : Usize) (hs : start.val ≤ finish.val)
      (hf : finish.val ≤ bytes.length) :
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes ⟨start, finish⟩ ⦃ region =>
          Wasm1.BytesAt bytes start region.val finish ⦄ := by
    step
    apply Wasm1.BytesAt.of_slice_view hs hf
    assumption
  obtain ⟨environment, he, heSpan⟩ := WP.spec_imp_exists
    (slice_spec 0#usize first (by simp) (by omega))
  obtain ⟨code, hc, hcSpan⟩ := WP.spec_imp_exists (slice_spec first last hfirst hlast)
  obtain ⟨tail, ht, htSpan⟩ := WP.spec_imp_exists
    (slice_spec last (Slice.len bytes) (by simpa using hlast) (by simp))
  exact ⟨environment, code, tail, he, hc, ht,
    by simpa using ((heSpan.append hcSpan).append htSpan).suffix⟩

end Itasca
