import Itasca.Runtime.Compiler.Module.CodeRegion
import Itasca.Stream.SplitComplete

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca ModuleBinary
set_option maxRecDepth 4096

private def compilerScan (data : Slice U8) (pos : Usize) :=
  runtime.compiler.code_region_loop data pos false (Slice.len data) (Slice.len data)

private theorem compiler_found (data : Slice U8) (pos first last : Usize) :
    runtime.compiler.code_region_loop data pos true first last = .ok (first,last) := by
  rw [runtime.compiler.code_region_loop,loop]
  simp only [runtime.compiler.code_region_loop.body]
  split <;> simp

private theorem compiler_split_body_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val ≤ 10 ∨ id.val = 12) :
    runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) =
      .ok (if id = 10#u8 then .cont (last,true,pos,last)
        else .cont (last,false,Slice.len data,Slice.len data)) := by
  obtain ⟨middle,count,header,decoded,lastValue,bounded⟩ := h
  obtain ⟨position,byte,advance⟩ := header.byte.single
  have read := Itasca.reader.read_u32_leb.complete data middle count first decoded
  have post : runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) ⦃ result =>
      result = if id = 10#u8 then .cont (last,true,pos,last) else .cont (last,false,Slice.len data,Slice.len data) ⦄ := by
    unfold runtime.compiler.code_region_loop.body
    have inside : pos < Slice.len data := by scalar_tac
    simp only [inside,↓reduceIte,Bool.false_eq_true]
    step as ⟨opcode,lookup⟩
    have actual : opcode = id := by simpa only [lookup] using byte
    simp only [actual,byte]
    by_cases high : id > 10#u8
    · have countId : id = 12#u8 := UScalar.eq_of_val_eq (by scalar_tac)
      simp only [high,↓reduceIte,countId,bne_self_eq_false,Bool.false_eq_true]
      step as ⟨advanced,advancedValue⟩
      have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
      subst advanced
      simp only [compiler_leb_eq,read,bind_ok,lift]
      step as ⟨remaining,remainingValue⟩
      step as ⟨finish,finishValue⟩
      have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
      subst finish
      split <;> simp_all
    · simp only [high,↓reduceIte]
      step as ⟨advanced,advancedValue⟩
      have same : advanced = middle := UScalar.eq_of_val_eq (by omega)
      subst advanced
      simp only [compiler_leb_eq,read,bind_ok,lift]
      step as ⟨remaining,remainingValue⟩
      step as ⟨finish,finishValue⟩
      have same : finish = last := UScalar.eq_of_val_eq (by scalar_tac)
      subst finish
      split <;> simp_all
  obtain ⟨result,called,same⟩ := WP.spec_imp_exists post
  exact called.trans (congrArg Result.ok same)

private theorem compiler_split_loop_eof (data : Slice U8) :
    compilerScan data (Slice.len data) = .ok (Slice.len data,Slice.len data) := by
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  simp [runtime.compiler.code_region_loop.body]

private theorem compiler_split_skip_section (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (allowed : id.val < 10 ∨ id.val = 12) :
    compilerScan data pos = compilerScan data last := by
  have body := compiler_split_body_section data pos first last id h (by omega)
  have notCode : id ≠ 10#u8 := by scalar_tac
  simp only [notCode,↓reduceIte] at body
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [body]
  simp only [bind_ok]
  unfold compilerScan runtime.compiler.code_region_loop
  rfl

private theorem compiler_split_code_section (data : Slice U8) (pos first last : Usize)
    (h : SectionHeader data pos 10#u8 first last) : compilerScan data pos = .ok (pos,last) := by
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [compiler_split_body_section data pos first last 10#u8 h (by decide)]
  simp only [↓reduceIte,bind_ok]
  exact compiler_found data last pos last

private theorem compiler_split_after_code (data : Slice U8) (pos first last : Usize) (id : U8)
    (h : SectionHeader data pos id first last) (high : 10 < id.val) (notCount : id.val ≠ 12) :
    compilerScan data pos = .ok (pos,pos) := by
  obtain ⟨_,_,header,_,_,_⟩ := h
  obtain ⟨position,byte,_⟩ := header.byte.single
  have post : runtime.compiler.code_region_loop.body data pos false (Slice.len data) (Slice.len data) ⦃ result =>
      result = .cont (pos,true,pos,pos) ⦄ := by
    unfold runtime.compiler.code_region_loop.body
    have inside : pos < Slice.len data := by scalar_tac
    simp only [inside,↓reduceIte,Bool.false_eq_true]
    step as ⟨opcode,lookup⟩
    have actual : opcode = id := by simpa only [lookup] using byte
    simp only [actual,byte]
    have above : id > 10#u8 := by scalar_tac
    have different : id ≠ 12#u8 := by intro same; have value := congrArg UScalar.val same; scalar_tac
    simp [above,different]
  obtain ⟨result,called,rfl⟩ := WP.spec_imp_exists post
  rw [compilerScan,runtime.compiler.code_region_loop,loop]
  dsimp only
  rw [called]
  simp only [bind_ok]
  exact compiler_found data pos pos pos

private theorem compiler_split_skip_customs {data : Slice U8} {bytes : List U8}
    (h : CustomsEncoding bytes) {pos next : Usize} (hb : Wasm1.BytesAt data pos bytes next) :
    compilerScan data pos =
      compilerScan data next := by
  induction h generalizing pos with
  | nil => rw [hb.empty]
  | cons hc _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨nm, payload, encodedName, _, hs⟩ := hc
    obtain ⟨content, hh, _⟩ := (show At
      (SectionEncoding 0#u8 (fun (_ : Unit) bs => bs = encodedName ++ payload))
      data pos () middle from ⟨_, hs, hfirst⟩).section_split
    rw [compiler_split_skip_section data pos content middle 0#u8 hh (by decide)]
    exact ih hrest

private theorem compiler_split_skip_chain {profile} {data : Slice U8} {raw n bytes}
    (h : ModuleEnv.Chain raw n bytes profile) {pos next : Usize}
    (hb : Wasm1.BytesAt data pos bytes next) :
    compilerScan data pos =
      compilerScan data next := by
  induction h generalizing pos with
  | done hc => exact compiler_split_skip_customs hc hb
  | @step profile n id first rest hn hid hslot _ ih =>
    obtain ⟨middle, hfirst, hrest⟩ := hb.split
    obtain ⟨customs, sec, hc, hs, he⟩ := hslot
    rw [he] at hfirst
    obtain ⟨afterCustoms, hcustoms, hsection⟩ := hfirst.split
    rw [compiler_split_skip_customs hc hcustoms]
    rcases hs with ⟨_, rfl⟩ | hs
    · rw [← hsection.empty]
      exact ih hrest
    · obtain ⟨content, hh, _⟩ := (show
        At (SectionEncoding id (fun u bs => ModuleEnv.Payload raw (sectionRank id).val u bs profile)) data afterCustoms () middle
        from ⟨_, hs, hsection⟩).section_split
      rw [compiler_split_skip_section data afterCustoms content middle id hh (by
        have hrange := sectionRank_prefix (id := id) (by omega) (by omega)
        omega)]
      exact ih hrest

theorem compiler_split_skip_prefix {profile} {data : Slice U8} {decls next}
    (h : At (fun ds bs => ModuleEnv.PrefixEncoding ds bs profile) data 0#usize decls next) :
    compilerScan data 8#usize =
      compilerScan data next := by
  obtain ⟨bytes, hp, hb⟩ := h
  obtain ⟨suffix, hc, he⟩ := hp.chain [] []
  rw [he] at hb
  obtain ⟨middle, hmagic, hchain⟩ := hb.split
  have hm : middle = 8#usize := by
    apply UScalar.eq_of_val_eq
    simpa [magicVersion] using hmagic.length
  subst middle
  exact compiler_split_skip_chain hc hchain

/-- On an independently valid normalized layout, the splitter returns the environment, code and
tail boundaries used by component completeness. -/
theorem compiler_code_region_complete_layout {profile} {data : Slice U8} {raw decls codePos tailPos}
    (h : ModuleLayout.Layout data raw decls codePos tailPos profile) :
    runtime.compiler.code_region data = .ok (codePos, tailPos) := by
  change compilerScan data 8#usize = _
  rw [compiler_split_skip_prefix h.environment]
  rcases h.code with hc | ⟨_, hsame, hstop⟩
  · obtain ⟨first, hh, _⟩ := hc.section_split
    exact compiler_split_code_section data codePos first tailPos hh
  · subst tailPos
    rcases hstop with heof | ⟨id, first, last, hh, hne⟩
    · have he : codePos = Slice.len data := by apply UScalar.eq_of_val_eq; simpa using heof
      rw [he]
      exact compiler_split_loop_eof data
    · rcases h.stop with heof | ⟨id', first', last', hh', hge⟩
      · have hs := hh.span
        have he := congrArg UScalar.val heof
        simp only [Slice.len_val] at he
        omega
      · have he : id = id' ∧ first = first' ∧ last = last' := by
          have hread := (module.read_section_header.complete data codePos id first last hh).symm.trans
            (module.read_section_header.complete data codePos id' first' last' hh')
          simpa using hread
        have hid : id = 11#u8 := by
          rcases hge with hc | hd
          · exact False.elim (hne (he.1.trans hc))
          · exact he.1.trans hd
        exact compiler_split_after_code data codePos first last id hh
          (by simp [hid]) (by simp [hid])


/-- On independently encoded modules, both concrete scanners select the same
canonical byte coordinates despite their different loop control states. -/
theorem compiler_code_region_eq_stream {profile} (data : Slice U8) (raw : ModuleBinary.Module)
    (encoded : ModuleEncodingWithinLimits raw data.val profile) :
    runtime.compiler.code_region data = Itasca.stream.find_code_region data := by
  obtain ⟨decls,codeStart,codeEnd,layout⟩ := ModuleLayout.normalize data raw encoded
  rw [compiler_code_region_complete_layout layout,Itasca.stream.find_code_region.complete_layout layout]

end Itasca.Runtime.Compiler
