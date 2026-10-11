import Itasca.Stream.StreamSliceSplit
import Itasca.Module.ModuleLayout
import Itasca.Module.ModuleEnvChain

open Aeneas Aeneas.Std

namespace Itasca
open ModuleBinary

theorem split_body_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : id.val ≤ 10) :
    stream.find_code_region_loop.body data (Slice.len data) pos =
      .ok (if id = 10#u8 then .done (pos, last)
        else if last = Slice.len data then .done (last, last) else .cont last) := by
  obtain ⟨middle, count, hb, hd, hlast, hbound⟩ := h
  obtain ⟨hp, hbyte, hmiddle⟩ := hb.byte.single
  obtain ⟨len, hlen, hlenval⟩ := stream.read_len.complete data middle first count hd
  have hs : stream.find_code_region_loop.body data (Slice.len data) pos ⦃ r =>
      r = if id = 10#u8 then .done (pos, last)
        else if last = Slice.len data then .done (last, last) else .cont last ⦄ := by
    unfold stream.find_code_region_loop.body
    have hn : ¬ pos ≥ Slice.len data := by scalar_tac
    simp only [hn, ↓reduceIte]
    step
    have hnid : ¬ id > module.SECTION_CODE := by simp [module.SECTION_CODE]; scalar_tac
    simp only [hnid, ↓reduceIte]
    step
    have he : i = middle := by apply UScalar.eq_of_val_eq; omega
    subst i
    simp only [hlen, bind_ok]
    step
    step
    step
    have he : «end» = last := by apply UScalar.eq_of_val_eq; scalar_tac
    subst «end»
    simp only [module.SECTION_CODE]
    split <;> split <;> simp_all
  obtain ⟨r, hr, he⟩ := WP.spec_imp_exists hs
  exact hr.trans (congrArg Result.ok he)

theorem split_loop_eof (data : Slice U8) :
    stream.find_code_region_loop data (Slice.len data) (Slice.len data) =
      .ok (Slice.len data, Slice.len data) := by
  rw [stream.find_code_region_loop, loop]
  simp [stream.find_code_region_loop.body]

theorem split_skip_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : id.val < 10) :
    stream.find_code_region_loop data (Slice.len data) pos =
      stream.find_code_region_loop data (Slice.len data) last := by
  have hb := split_body_section data pos first last id h (by omega)
  have hn : id ≠ 10#u8 := by scalar_tac
  simp only [hn, ↓reduceIte] at hb
  by_cases hend : last = Slice.len data
  · rw [hend, split_loop_eof]
    rw [stream.find_code_region_loop, loop, hb]
    simp [hend]
  · unfold stream.find_code_region_loop
    rw [loop, hb]
    simp [hend]

private theorem split_code_section (data : Slice U8) (pos first last : Usize)
    (h : SectionHeader data pos 10#u8 first last) :
    stream.find_code_region_loop data (Slice.len data) pos = .ok (pos, last) := by
  rw [stream.find_code_region_loop, loop, split_body_section data pos first last 10#u8 h (by decide)]
  simp

private theorem split_after_code (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (hid : 10 < id.val) :
    stream.find_code_region_loop data (Slice.len data) pos = .ok (pos, pos) := by
  obtain ⟨_, _, hb, _, _, _⟩ := h
  obtain ⟨hp, hbyte, _⟩ := hb.byte.single
  have hs : stream.find_code_region_loop.body data (Slice.len data) pos ⦃ r =>
      r = .done (pos, pos) ⦄ := by
    unfold stream.find_code_region_loop.body
    have hn : ¬ pos ≥ Slice.len data := by scalar_tac
    simp only [hn, ↓reduceIte]
    step
    have hnid : id > module.SECTION_CODE := by simp [module.SECTION_CODE]; scalar_tac
    simp [hnid]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  rw [stream.find_code_region_loop, loop, hr]
  simp

private theorem split_skip_customs {data : Slice U8} {bytes : List U8}
    (h : CustomsEncoding bytes) {pos next : Usize} (hb : Wasm.BytesAt data pos bytes next) :
    stream.find_code_region_loop data (Slice.len data) pos =
      stream.find_code_region_loop data (Slice.len data) next := by
  induction h generalizing pos with
  | nil => rw [hb.empty]
  | cons hc _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨nm, payload, encodedName, _, hs⟩ := hc
    obtain ⟨content, hh, _⟩ := (show At
      (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload))
      data pos () middle from ⟨_, hs, hfirst⟩).section_split
    rw [split_skip_section data pos content middle 0#u8 hh (by decide)]
    exact ih hrest

private theorem split_skip_chain {profile} {data : Slice U8} {raw n bytes}
    (h : ModuleEnv.Chain raw n bytes profile) {pos next : Usize}
    (hb : Wasm.BytesAt data pos bytes next) :
    stream.find_code_region_loop data (Slice.len data) pos =
      stream.find_code_region_loop data (Slice.len data) next := by
  induction h generalizing pos with
  | done hc => exact split_skip_customs hc hb
  | @step profile n id first rest hn hid hslot _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨customs, sec, hc, hs, he⟩ := hslot
    rw [he] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    rw [split_skip_customs hc hcustoms]
    rcases hs with ⟨_, rfl⟩ | hs
    · rw [← hsection.empty]
      exact ih hrest
    · obtain ⟨content, hh, _⟩ := (show
        At (SectionEncoding id (fun u bs => ModuleEnv.Payload raw id.val u bs profile)) data afterCustoms () middle
        from ⟨_, hs, hsection⟩).section_split
      rw [split_skip_section data afterCustoms content middle id hh (by omega)]
      exact ih hrest

theorem split_skip_prefix {profile} {data : Slice U8} {decls next}
    (h : At (fun ds bs => ModuleEnv.PrefixEncoding ds bs profile) data 0#usize decls next) :
    stream.find_code_region_loop data (Slice.len data) 8#usize =
      stream.find_code_region_loop data (Slice.len data) next := by
  obtain ⟨bytes, hp, hb⟩ := h
  obtain ⟨suffix, hc, he⟩ := hp.chain [] []
  rw [he] at hb
  obtain ⟨middle, hmagic, hchain⟩ := hb.split
  have hm : middle = 8#usize := by
    apply UScalar.eq_of_val_eq
    simpa [magicVersion] using hmagic.length
  subst middle
  exact split_skip_chain hc hchain

/-- On an independently valid normalized layout, the concrete splitter chooses
exactly the environment/code/tail boundaries used by component completeness. -/
theorem stream.find_code_region.complete_layout {profile} {data : Slice U8} {raw decls codePos tailPos}
    (h : ModuleLayout.Layout data raw decls codePos tailPos profile) :
    stream.find_code_region data = .ok (codePos, tailPos) := by
  simp only [stream.find_code_region]
  rw [split_skip_prefix h.environment]
  rcases h.code with hc | ⟨_, hsame, hstop⟩
  · obtain ⟨first, hh, _⟩ := hc.section_split
    exact split_code_section data codePos first tailPos hh
  · subst tailPos
    rcases hstop with heof | ⟨id, first, last, hh, hne⟩
    · have he : codePos = Slice.len data := by apply UScalar.eq_of_val_eq; simpa using heof
      rw [he]
      exact split_loop_eof data
    · rcases h.stop with heof | ⟨id', first', last', hh', hge⟩
      · have hs := hh.span
        have he := congrArg UScalar.val heof
        simp only [Slice.len_val] at he
        omega
      · have he : id = id' ∧ first = first' ∧ last = last' := by
          have hread := (module.read_section_header.complete data codePos id first last hh).symm.trans
            (module.read_section_header.complete data codePos id' first' last' hh')
          simpa using hread
        exact split_after_code data codePos first last id hh (by
          have hne' : id.val ≠ 10 := by intro heq; apply hne; apply UScalar.eq_of_val_eq; exact heq
          rw [he.1] at hne' ⊢
          omega)

/-- Independent module encoding supplies canonical splitter boundaries without
assuming any successful parser run. -/
theorem stream.find_code_region.complete {profile} (data : Slice U8) (raw : ModuleBinary.Module)
    (h : ModuleEncodingWithinLimits raw data.val profile) :
    ∃ decls codePos tailPos, ModuleLayout.Layout data raw decls codePos tailPos profile ∧
      stream.find_code_region data = .ok (codePos, tailPos) := by
  obtain ⟨decls, codePos, tailPos, hl⟩ := ModuleLayout.normalize data raw h
  exact ⟨decls, codePos, tailPos, hl, stream.find_code_region.complete_layout hl⟩

end Itasca
