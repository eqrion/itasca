import Itasca.Stream.EntryFrame
import Itasca.Support.Result

/-!
# Code section header

Soundness and termination for `stream.read_code_header`, which reads at most the first 11 bytes of
the code region and checks the section ID, the section size and the function count against the
environment. `StreamFraming.HeaderChecked` describes what the driver observed through the source,
and `StreamFraming.HeaderAt` is the resulting fact about the coherent code region, with an absent
region and a present zero-entry section as separate cases. Completeness is in
`Stream/HeaderComplete`.
-/

open Aeneas Aeneas.Std

namespace Itasca

namespace StreamFraming

/-- The driver observes either an absent code region or an exact bounded
header view. Counts and section size are independent of entry validation. -/
def HeaderChecked {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : module.Env) (entries : Usize) : Prop :=
  (codeLen = 0#usize ∧ entries = 0#usize ∧ env.func_type_indices.val = []) ∨
  ∃ header content size count,
    stream.read_exact source state 0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) =
      .ok (.Ok header) ∧
    ModuleBinary.At ModuleBinary.ByteEncoding header 0#usize 10#u8 1#usize ∧
    Leb128.Decoded header 1#usize size content ∧
    codeLen.val = content.val + size.val ∧
    Leb128.Decoded header content count entries ∧
    entries.val ≤ codeLen.val ∧ count.val = env.func_type_indices.val.length

theorem header_limit : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
  have hs : limits.MAX_CODE_HEADER_BYTES ⦃ x => x = 11#usize ⦄ := by
    unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
    step*
  obtain ⟨x, hx, rfl⟩ := WP.spec_imp_exists hs
  exact hx

theorem min_val (a b : Usize) :
    (core.cmp.impls.OrdUsize.min a b).val = Nat.min a.val b.val := by
  simp only [core.cmp.impls.OrdUsize.min]
  split <;> simp_all [Nat.min_def]

end StreamFraming

/-- `stream.read_code_header` either errors or returns the entry count of a checked header,
provided the reached code read returns. -/
theorem stream.read_code_header.spec {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : module.Env)
    (hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r) :
    stream.read_code_header source state codeLen env ⦃ r => match r with
      | .Ok entries => StreamFraming.HeaderChecked source state codeLen env entries
      | .Err _ => True ⦄ := by
  unfold stream.read_code_header
  dsimp only
  split
  · rename_i hzero
    simp [alloc.vec.Vec.is_empty]
    split
    · rename_i hempty
      simp only [WP.spec_ok]
      exact .inl ⟨hzero, rfl, by simpa using hempty⟩
    · simp
  · rename_i hnonzero
    rw [StreamFraming.header_limit]
    simp only [bind_ok, lift]
    obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (stream.read_exact.spec source state
      0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) (by simp) (hreturn hnonzero))
    rw [hr]
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok header =>
      have hlen : header.length = Nat.min codeLen.val 11 := by
        simpa [StreamFraming.min_val] using hp.2
      have hpositive : 0 < header.length := by
        have hn : codeLen.val ≠ 0 := by intro he; apply hnonzero; exact UScalar.eq_of_val_eq he
        rw [hlen]
        exact Nat.lt_min.mpr ⟨by omega, by decide⟩
      obtain ⟨id, hid, hidval⟩ := WP.spec_imp_exists (Slice.index_usize_spec header 0#usize hpositive)
      simp [core.result.Result.Insts.CoreOpsTry.branch, hid]
      split
      · rename_i hiscode
        have hidcode : id = 10#u8 := by
          apply UScalar.eq_of_val_eq
          simpa [module.SECTION_CODE] using hiscode
        have hbyte : ModuleBinary.At ModuleBinary.ByteEncoding header 0#usize 10#u8 1#usize :=
          ⟨[10#u8], rfl, Wasm1.BytesAt.byte header 0#usize 1#usize 10#u8 hpositive
            (by simpa [hidcode] using hidval.symm) (by simp)⟩
        obtain ⟨r, hs, hsp⟩ := WP.spec_imp_exists (stream.read_len.spec header 1#usize)
        rw [hs]
        cases r with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok pair =>
          obtain ⟨len, content⟩ := pair
          obtain ⟨size, hsizeval, hsize⟩ := hsp
          simp
          obtain ⟨r, he, hep⟩ := WP.spec_imp_exists (limits.add_offset.spec content len)
          rw [he]
          cases r with
          | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok finish =>
            simp
            split
            · simp
            · rename_i hnotover
              split
              · simp
              · rename_i hnotunder
                have hend : codeLen.val = content.val + size.val := by omega
                obtain ⟨r, hc, hcp⟩ := WP.spec_imp_exists (stream.read_len.spec header content)
                rw [hc]
                cases r with
                | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                | Ok pair =>
                  obtain ⟨countLen, entries⟩ := pair
                  obtain ⟨count, hcountval, hcount⟩ := hcp
                  simp
                  split
                  · simp
                  · rename_i hentries
                    split
                    · rename_i hcountlen
                      simp only [WP.spec_ok]
                      change ¬ entries.val > finish.val at hentries
                      change countLen.val = env.func_type_indices.val.length at hcountlen
                      exact .inr ⟨header, content, size, count, hr, hbyte, hsize, hend,
                        hcount, by omega, by omega⟩
                    · simp
      · simp

/-- Header termination requires only the reached source read to return an
ordinary result; malformed headers and read errors remain covered. -/
theorem stream.read_code_header.total {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : module.Env)
    (htotal : StreamSource.CallbacksTotal source state) :
    ∃ r, stream.read_code_header source state codeLen env = .ok r := by
  obtain ⟨r, hr, _⟩ := WP.spec_imp_exists
    (stream.read_code_header.spec source state codeLen env (fun _ => htotal.code_returns _ _))
  exact ⟨r, hr⟩

/-- Acceptance itself supplies the reached source callback. No premise is
imposed on unrelated or unexecuted source calls. -/
theorem stream.read_code_header.checked {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : module.Env) (entries : Usize)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    StreamFraming.HeaderChecked source state codeLen env entries := by
  have hreturn : codeLen ≠ 0#usize → ∃ r, source.code state 0#usize
      (core.cmp.impls.OrdUsize.min codeLen 11#usize) = .ok r := by
    intro hnonzero
    unfold stream.read_code_header at h
    rw [if_neg hnonzero, StreamFraming.header_limit] at h
    simp only [bind_ok, lift] at h
    obtain ⟨r, hr, hrest⟩ := ResultFacts.bind_ok_inv _ _ _ h
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at hrest
    | Ok header =>
      exact ⟨.Ok header, (stream.read_exact.accepted source state _ _ header (by simp) hr).1⟩
  have hs := stream.read_code_header.spec source state codeLen env hreturn
  simpa [h] using hs

namespace StreamFraming

/-- The code region is either empty with no declared functions, or a code section whose size
covers the whole region. A present zero-entry section is distinct from an absent one. -/
def HeaderAt (data : Slice U8) (env : module.Env) (entries : Usize) : Prop :=
  (data.val = [] ∧ entries = 0#usize ∧ env.func_type_indices.val = []) ∨
    ∃ count, ModuleCode.Section data 0#usize env ⟨count, entries, Slice.len data⟩ ∧
      entries.val ≤ data.length

theorem HeaderChecked.sound {S : Type} {source : stream.Source S} {state : S}
    {codeLen : Usize} {env : module.Env} {entries : Usize} {data : Slice U8}
    {environment tail : List U8}
    (h : HeaderChecked source state codeLen env entries)
    (hcoherent : StreamSource.Coherent source state environment data.val tail)
    (hsize : codeLen.val = data.length) : HeaderAt data env entries := by
  rcases h with ⟨hlen, hentries, hempty⟩ |
    ⟨header, content, size, count, hread, hbyte, hlength, hend, hcount, hbound, hcountval⟩
  · refine .inl ⟨?_, hentries, hempty⟩
    simpa [hlen, Slice.length] using hsize.symm
  · have hviewbound : (core.cmp.impls.OrdUsize.min codeLen 11#usize).val ≤ data.length := by
      rw [min_val, hsize]
      exact Nat.min_le_left _ _
    have hview := (stream.read_exact.sound source state environment data.val tail hcoherent
      0#usize (core.cmp.impls.OrdUsize.min codeLen 11#usize) header (by simp) hviewbound hread).1
    have hspan := Wasm1.BytesAt.of_slice_view (by simp) hviewbound hview
    have hid : ModuleBinary.At ModuleBinary.ByteEncoding data 0#usize 10#u8 1#usize := by
      obtain ⟨bs, hb, hs⟩ := hbyte
      exact ⟨bs, hb, hspan.transport hs (by simp) (by simp)⟩
    have hlength' := hlength.of_slice_view (by simp) hviewbound hview
      (pos' := 1#usize) (next' := content) (by simp) (by simp)
    have hcount' := hcount.of_slice_view (by simp) hviewbound hview
      (pos' := content) (next' := entries) (by simp) (by simp)
    refine .inr ⟨count, ⟨content, ?_, hcount', hcountval⟩, by omega⟩
    exact ⟨1#usize, size, hid, hlength', by simpa [hsize] using hend, by simp⟩

end StreamFraming

/-- Over a coherent source, a successful `stream.read_code_header` returns the entry count of a
code section that spans the whole code region. -/
theorem stream.read_code_header.sound {S : Type} (source : stream.Source S) (state : S)
    (codeLen : Usize) (env : module.Env) (entries : Usize) (data : Slice U8)
    (environment tail : List U8)
    (hcoherent : StreamSource.Coherent source state environment data.val tail)
    (hsize : codeLen.val = data.length)
    (h : stream.read_code_header source state codeLen env = .ok (.Ok entries)) :
    StreamFraming.HeaderAt data env entries :=
  (stream.read_code_header.checked source state codeLen env entries h).sound hcoherent hsize

end Itasca
