import Itasca.Main
import Itasca.Examples.Module.Basic
import Itasca.Examples.Module.Support

/-!
# Rejected modules

Wasm 1.0 modules that `module.validate_module` rejects, each with the exact error: a duplicate
export name written in four-byte UTF-8, an unknown start function or type index, a bad function
type form byte, truncated counts and section payloads, a repeated section, and a section whose
declared size exceeds its contents. Each case is a short byte string, so the examples show that
errors found while decoding sections reach the public entry point unchanged.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleNegative

open ModuleSupport (leb)

open ModuleBinary ModuleEnv

private theorem section_header (data : Slice U8) (pos middle first last : Usize)
    (id count : U8) (hcount : count.val < 128)
    (hi : Wasm1.BytesAt data pos [id] middle)
    (hc : Wasm1.BytesAt data middle [count] first)
    (he : last.val = first.val + count.val) (hb : last.val ≤ data.length) :
    SectionHeader data pos id first last := by
  let size := U32.ofNatCore count.val (by scalar_tac)
  exact ⟨middle, size, ⟨[id], rfl, hi⟩,
    hc.u32_decoded size (by simpa [size] using leb count hcount),
    by simpa [size] using he, hb⟩

private theorem env_from_loop (data : Slice U8)
    (hbytes : Wasm1.BytesAt data 0#usize magicVersion 8#usize) (e : error.Error)
    (hloop : parseLoop data Examples.ModuleBasic.emptyEnv 8#usize 0#u8 = .ok (.Err e, ())) :
    module.validate_env data .Wasm1 = .ok (.Err e) := by
  have hh := module.read_header.complete data 8#usize hbytes
  simp only [parseLoop, Examples.ModuleBasic.emptyEnv] at hloop
  simp [module.validate_env, module.validate_env_with, module.Env.new,
    hh, core.result.Result.Insts.CoreOpsTry.branch, hloop]

/-- A module with one memory and two exports of it, both named by the four bytes of U+10FFFF.
The names are valid UTF-8 and the indices are valid, so only the duplicate name is an error. -/
def duplicateUnicodeExports : Slice U8 := Examples.ModuleSupport.bytes
  (magicVersion ++ [5#u8,3#u8,1#u8,0#u8,0#u8,
    7#u8,15#u8,2#u8,4#u8,0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8,2#u8,0#u8,
    4#u8,0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8,2#u8,0#u8])
  (by simp [magicVersion]; scalar_tac)

private theorem duplicate_exports_decode (env : module.Env)
    (he : env.exports.val = []) (hm : env.mem_types.val.length = 1) :
    ∃ result, module.decode_export_section duplicateUnicodeExports 15#usize env =
      .ok (.Err .DuplicateExportName, result) := by
  let data := duplicateUnicodeExports
  let nm := alloc.vec.Vec.from [0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8]
    (by simp; scalar_tac)
  have hnm : NameEncoding nm.val [4#u8,0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8] := by
    refine ⟨ByteVecEncoding.iff.mpr ⟨[4#u8], leb 4#u8, by simp [nm]⟩, ?_⟩
    exact .cons (.four _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)) .nil
  have hname1 := module.decode_name.complete data 16#usize nm 21#usize
    ⟨_, hnm, by constructor <;> simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes,
      alloc.vec.Vec.deref, magicVersion]⟩
  have hname2 := module.decode_name.complete data 23#usize nm 28#usize
    ⟨_, hnm, by constructor <;> simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes,
      alloc.vec.Vec.deref, magicVersion]⟩
  have hcount := (show At IndexEncoding data 15#usize 2#u32 16#usize from
    ⟨[2#u8], leb 2#u8, by constructor <;> simp [data, duplicateUnicodeExports,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hkind := (show At ByteEncoding data 21#usize 2#u8 22#usize from
    ⟨[2#u8], rfl, by constructor <;> simp [data, duplicateUnicodeExports,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_byte
  have hindex := (show At IndexEncoding data 22#usize 0#u32 23#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, duplicateUnicodeExports,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hfresh := module.export_name_taken.fresh env (alloc.vec.Vec.deref nm) (by simp [he])
  have hdesc := module.export_desc.complete env (.Memory 0#u32)
    (by simp [ModuleSections.ExportDescValid, hm])
  simp only [ModuleSections.descByte, ModuleSections.descIndex] at hdesc
  obtain ⟨exports, hpush, hexports⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.push_spec env.exports (⟨nm, .Memory 0#u32⟩ : module.Export) (by simp [he]; scalar_tac))
  let updated := { env with exports := exports }
  have hduplicate := module.export_name_taken.duplicate updated (alloc.vec.Vec.deref nm)
    (by simp [updated, hexports, he, alloc.vec.Vec.deref])
  have hinc : (0#u32 + 1#u32 : Result U32) = .ok 1#u32 := by
    have hs : (0#u32 + 1#u32 : Result U32) ⦃ n => n = 1#u32 ⦄ := by step*
    obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
    exact hr
  have hbody : module.decode_export_section_loop.body data 2#u32 env 16#usize 0#u32 =
      .ok (.cont (updated, 23#usize, 1#u32)) := by
    simp [module.decode_export_section_loop.body, hname1, hfresh, hkind, hindex,
      hdesc, hpush, hinc, core.result.Result.Insts.CoreOpsTry.branch, updated]
  have hloop : module.decode_export_section_loop data env 2#u32 16#usize 0#u32 =
      .ok (.Err .DuplicateExportName, updated) := by
    unfold module.decode_export_section_loop
    rw [loop]
    simp only [hbody, bind_ok]
    rw [loop]
    simp [module.decode_export_section_loop.body, hname2, hduplicate,
      core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨updated, by simp [module.decode_export_section, hcount, hloop,
    core.result.Result.Insts.CoreOpsTry.branch, data]⟩

/-- `duplicateUnicodeExports` is rejected with `DuplicateExportName`. -/
theorem duplicate_unicode_exports_rejected : module.validate_module duplicateUnicodeExports .Wasm1 =
    .ok (.Err .DuplicateExportName) := by
  let data := duplicateUnicodeExports
  let mt : types.MemType := ⟨⟨0#u32, none⟩⟩
  have hmem : At (VecEncoding MemTypeEncoding) data 10#usize [mt] 13#usize := by
    refine ⟨[1#u8,0#u8,0#u8], ⟨[1#u8], [0#u8,0#u8], leb 1#u8, ?_, rfl⟩, ?_⟩
    · exact .cons (show MemTypeEncoding mt [0#u8,0#u8] from
        LimitsEncoding.noMax 0#u32 (leb 0#u8)) .nil
    · constructor <;> simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes,
        alloc.vec.Vec.deref, magicVersion]
  obtain ⟨env, hread, hadded⟩ := module.decode_memory_section.complete data 10#usize
    Examples.ModuleBasic.emptyEnv [mt] 13#usize hmem
    (by
      intro ty ht
      have ht : ty = mt := by simpa using ht
      subst ty
      simp [mt, LimitsValid, limits.MAX_MEMORY_PAGES])
    (by simp [Examples.ModuleBasic.emptyEnv])
  have he : env.exports.val = [] := by rw [hadded.1]; rfl
  have hm : env.mem_types.val.length = 1 := by simp [hadded.2, Examples.ModuleBasic.emptyEnv]
  obtain ⟨result, hexport⟩ := duplicate_exports_decode env he hm
  change module.decode_export_section data 15#usize env = _ at hexport
  have hhmem : SectionHeader data 8#usize 5#u8 10#usize 13#usize := by
    apply section_header data 8#usize 9#usize 10#usize 13#usize 5#u8 3#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, duplicateUnicodeExports,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]) |
      simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hstep := module.validate_env_with_loop.complete_section (profile := .Wasm1) data Examples.ModuleBasic.emptyEnv
    env 8#usize 10#usize 13#usize 0#u8 5#u8 hhmem (by decide) (by decide) (by decide)
    (by simpa [module.decode_env_section, global_simps] using hread)
  have hhexport : SectionHeader data 13#usize 7#u8 15#usize 30#usize := by
    apply section_header data 13#usize 14#usize 15#usize 30#usize 7#u8 15#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, duplicateUnicodeExports,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hheader := module.read_section_header.complete data 13#usize 7#u8 15#usize 30#usize hhexport
  have hmore : ¬ 13#usize ≥ Slice.len data := by
    simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hloop : parseLoop data env 13#usize 5#u8 = .ok (.Err .DuplicateExportName, ()) := by
    unfold parseLoop module.validate_env_with_loop
    rw [loop]
    simp [module.validate_env_with_loop.body, module.section_order, hmore, hheader, global_simps,
      module.decode_env_section, hexport, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize 10#usize 13#usize 5#u8 hhmem (by decide),
      split_skip_section data 13#usize 15#usize 30#usize 7#u8 hhexport (by decide)]
    exact split_loop_eof data
  apply Examples.ModuleBasic.environment_error data _
    (by simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref,
      magicVersion, limits.MAX_MODULE_BYTES]) hsplit
  apply env_from_loop data (by constructor <;> simp [data, duplicateUnicodeExports, Examples.ModuleSupport.bytes,
    alloc.vec.Vec.deref, magicVersion]) _
  rw [hstep]
  exact hloop

private theorem first_section_error (data : Slice U8)
    (hbytes : Wasm1.BytesAt data 0#usize magicVersion 8#usize) (id : U8) (first last : Usize)
    (e : error.Error) (updated : module.Env) (hmore : 8 < data.length)
    (hlo : 0 < id.val) (hhi : id.val < 10)
    (hsection : SectionHeader data 8#usize id first last)
    (hfinish : last = Slice.len data)
    (hread : module.decode_env_section data first id Examples.ModuleBasic.emptyEnv .Wasm1 = .ok (.Err e, updated))
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val) :
    module.validate_module data .Wasm1 = .ok (.Err e) := by
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize first last id hsection (.inl hhi), hfinish, split_loop_eof]
  have hheader := module.read_section_header.complete data 8#usize id first last hsection
  apply Examples.ModuleBasic.environment_error data e hsize hsplit
  apply env_from_loop data hbytes e
  have hstop : ¬ 8#usize ≥ Slice.len data := by scalar_tac
  have hcustom : id ≠ module.SECTION_CUSTOM := by
    intro he; have := congrArg UScalar.val he; simp [module.SECTION_CUSTOM] at this; omega
  have hcode : id ≠ module.SECTION_CODE := by simp only [global_simps]; scalar_tac
  have hdata : id ≠ module.SECTION_DATA := by simp only [global_simps]; scalar_tac
  have hrank : module.section_order id = .ok (.Ok id) := by
    simp [module.section_order, show 1#u8 ≤ id by scalar_tac,
      show id ≤ 9#u8 by scalar_tac]
  have horder : id.val ≠ 0 := by omega
  unfold parseLoop module.validate_env_with_loop
  rw [loop]
  simp [module.validate_env_with_loop.body, hstop, hheader, hcustom, hcode, hdata, hrank, horder,
    hread, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- A module with one section with the given id and declared size, followed by one payload
byte. -/
def shortSection (id size payload : U8) : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [id,size,payload]) (by simp [magicVersion]; scalar_tac)

/-- A module with one section with the given id and size 0. -/
def emptySection (id : U8) : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [id,0#u8]) (by simp [magicVersion]; scalar_tac)

/-- A type section with one type whose form byte is `0x00` instead of `0x60`. -/
def invalidType : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [1#u8,2#u8,1#u8,0#u8]) (by simp [magicVersion]; scalar_tac)

private theorem empty_section_header (id : U8) :
    SectionHeader (emptySection id) 8#usize id 10#usize 10#usize := by
  apply section_header (emptySection id) 8#usize 9#usize 10#usize 10#usize id 0#u8 (by decide)
  all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [emptySection,
    Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])

/-- A start section naming function 0 in a module with no functions is rejected with
`UnknownFunc 0`. -/
theorem invalid_start_index_rejected : module.validate_module (shortSection 8#u8 1#u8 0#u8) .Wasm1 =
    .ok (.Err (.UnknownFunc 0#u32)) := by
  let data := shortSection 8#u8 1#u8 0#u8
  have hh : SectionHeader data 8#usize 8#u8 10#usize 11#usize := by
    apply section_header data 8#usize 9#usize 10#usize 11#usize 8#u8 1#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, shortSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hr := (show At IndexEncoding data 10#usize 0#u32 11#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, shortSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  apply first_section_error data (by constructor <;> simp [data, shortSection, Examples.ModuleSupport.bytes,
    alloc.vec.Vec.deref, magicVersion]) 8#u8 10#usize 11#usize _ Examples.ModuleBasic.emptyEnv
    (by simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
    (by decide) (by decide) hh rfl
  · simp [module.decode_env_section, module.decode_start_section, global_simps, hr, lift,
      Examples.ModuleBasic.emptyEnv, core.result.Result.Insts.CoreOpsTry.branch]
  · simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]

/-- `invalidType` is rejected with `InvalidType 0`, carrying the bad form byte. -/
theorem invalid_function_type_rejected : module.validate_module invalidType .Wasm1 =
    .ok (.Err (.InvalidType 0#u8)) := by
  let data := invalidType
  have hh : SectionHeader data 8#usize 1#u8 10#usize 12#usize := by
    apply section_header data 8#usize 9#usize 10#usize 12#usize 1#u8 2#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, invalidType,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hc := (show At IndexEncoding data 10#usize 1#u32 11#usize from
    ⟨[1#u8], leb 1#u8, by constructor <;> simp [data, invalidType,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have ht := (show At ByteEncoding data 11#usize 0#u8 12#usize from
    ⟨[0#u8], rfl, by constructor <;> simp [data, invalidType,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_byte
  have hd : module.decode_type_section data 10#usize Examples.ModuleBasic.emptyEnv .Wasm1 =
      .ok (.Err (.InvalidType 0#u8), Examples.ModuleBasic.emptyEnv) := by
    simp [module.decode_type_section, hc, core.result.Result.Insts.CoreOpsTry.branch]
    unfold module.decode_type_section_loop
    rw [loop]
    simp [module.decode_type_section_loop.body, module.decode_func_type, ht,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply first_section_error data (by constructor <;> simp [data, invalidType, Examples.ModuleSupport.bytes,
    alloc.vec.Vec.deref, magicVersion]) 1#u8 10#usize 12#usize _ Examples.ModuleBasic.emptyEnv
    (by simp [data, invalidType, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
    (by decide) (by decide) hh rfl
  · simpa [module.decode_env_section, global_simps] using hd
  · simp [data, invalidType, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]

/-- A type section of size 0 has no room for its count, so the module is rejected with
`Read UnexpectedEof`. -/
theorem truncated_type_count_rejected : module.validate_module (emptySection 1#u8) .Wasm1 =
    .ok (.Err (.Read .UnexpectedEof)) := by
  let data := emptySection 1#u8
  have heof := reader.read_u32_leb.reject_complete data 10#usize .UnexpectedEof
    (.eof [] (by simp [data, emptySection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
      (by simp) (by simp))
  apply first_section_error data (by constructor <;> simp [data, emptySection, Examples.ModuleSupport.bytes,
    alloc.vec.Vec.deref, magicVersion]) 1#u8 10#usize 10#usize _ Examples.ModuleBasic.emptyEnv
    (by simp [data, emptySection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
    (by decide) (by decide)
    (empty_section_header 1#u8) rfl
  · simp [module.decode_env_section, module.decode_type_section, global_simps, heof,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      error.Error.Insts.CoreConvertFromOpError.from]
  · simp [data, emptySection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]

/-- A type section declaring size 2 with one payload byte is rejected with `UnexpectedEof`. -/
theorem truncated_section_payload_rejected : module.validate_module (shortSection 1#u8 2#u8 0#u8) .Wasm1 =
    .ok (.Err .UnexpectedEof) := by
  let data := shortSection 1#u8 2#u8 0#u8
  have hid := (show At ByteEncoding data 8#usize 1#u8 9#usize from
    ⟨[1#u8], rfl, by constructor <;> simp [data, shortSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_byte
  have hsize := (show At IndexEncoding data 9#usize 2#u32 10#usize from
    ⟨[2#u8], leb 2#u8, by constructor <;> simp [data, shortSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  obtain ⟨r, hr, _, herr⟩ := WP.spec_imp_exists (module.have_bytes.spec data 10#usize
    (UScalar.cast .Usize 2#u32)
    (by simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]))
  have he : r = .Err .UnexpectedEof := herr.mpr
    (by simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  subst r
  have hh : module.read_section_header data 8#usize = .ok (.Err .UnexpectedEof) := by
    simp [module.read_section_header, hid, hsize, hr, lift,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    have hlen : stream.read_len data 9#usize = .ok (.Ok (2#usize,10#usize)) := by
      have hs : stream.read_len data 9#usize ⦃ r => r = .Ok (2#usize,10#usize) ⦄ := by
        simp [stream.read_len,hsize]
        step*
        have hi : i = 2#usize := by
          apply UScalar.eq_of_val_eq
          scalar_tac
        simp [hi]
      obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
      exact hr
    have hb : stream.find_code_region_loop.body data 11#usize 8#usize = .ok (.done (11#usize,11#usize)) := by
      have hs : stream.find_code_region_loop.body data 11#usize 8#usize ⦃ r => r = .done (11#usize,11#usize) ⦄ := by
        unfold stream.find_code_region_loop.body
        simp only [show ¬ 8#usize ≥ 11#usize by decide, ↓reduceIte]
        step
        · simp [data,shortSection,Examples.ModuleSupport.bytes,alloc.vec.Vec.deref,magicVersion]
        have hi : id = 1#u8 := by simpa [data,shortSection,Examples.ModuleSupport.bytes,alloc.vec.Vec.deref,magicVersion] using id_post
        subst id
        rw [hi]
        simp only [module.SECTION_CODE]
        simp only [show ¬ 1#u8 > 10#u8 by decide, ↓reduceIte]
        step
        have hi : i = 9#usize := by scalar_tac
        subst i
        simp only [hlen,bind_ok]
        step*
      obtain ⟨_,hr,rfl⟩ := WP.spec_imp_exists hs
      exact hr
    unfold stream.find_code_region stream.find_code_region_loop
    rw [loop]
    have hl : Slice.len data = 11#usize := rfl
    rw [hl,hb]
    simp
  apply Examples.ModuleBasic.environment_error data _
    (by simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]) hsplit
  apply env_from_loop data (by constructor <;> simp [data, shortSection,
    Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]) _
  have hmore : ¬ 8#usize ≥ Slice.len data := by
    simp [data, shortSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  unfold parseLoop module.validate_env_with_loop
  rw [loop]
  simp [module.validate_env_with_loop.body, hmore, hh, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Two consecutive type sections, each holding an empty vector. -/
def repeatedTypeSection : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [1#u8,1#u8,0#u8,1#u8,1#u8,0#u8])
    (by simp [magicVersion]; scalar_tac)

/-- A repeated type section is rejected with `SectionOutOfOrder`. -/
theorem repeated_type_section_rejected : module.validate_module repeatedTypeSection .Wasm1 =
    .ok (.Err .SectionOutOfOrder) := by
  let data := repeatedTypeSection
  have hfirst : SectionHeader data 8#usize 1#u8 10#usize 11#usize := by
    apply section_header data 8#usize 9#usize 10#usize 11#usize 1#u8 1#u8 (by decide)
    · constructor <;> simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
    · constructor <;> simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
    · rfl
    · simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hsecond : SectionHeader data 11#usize 1#u8 13#usize 14#usize := by
    apply section_header data 11#usize 12#usize 13#usize 14#usize 1#u8 1#u8 (by decide)
    · constructor <;> simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
    · constructor <;> simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
    · rfl
    · simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hcount := (show At IndexEncoding data 10#usize 0#u32 11#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, repeatedTypeSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hread : module.decode_env_section data 10#usize 1#u8 Examples.ModuleBasic.emptyEnv .Wasm1 =
      .ok (.Ok 11#usize, Examples.ModuleBasic.emptyEnv) := by
    simp [module.decode_env_section, module.decode_type_section, global_simps, hcount,
      core.result.Result.Insts.CoreOpsTry.branch]
    unfold module.decode_type_section_loop
    rw [loop]
    simp [module.decode_type_section_loop.body]
  have hstep := module.validate_env_with_loop.complete_section (profile := .Wasm1) data Examples.ModuleBasic.emptyEnv
    Examples.ModuleBasic.emptyEnv 8#usize 10#usize 11#usize 0#u8 1#u8 hfirst
    (by decide) (by decide) (by decide) hread
  have hheader := module.read_section_header.complete data 11#usize 1#u8 13#usize 14#usize hsecond
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize 10#usize 11#usize 1#u8 hfirst (by decide),
      split_skip_section data 11#usize 13#usize 14#usize 1#u8 hsecond (by decide)]
    exact split_loop_eof data
  apply Examples.ModuleBasic.environment_error data _
    (by simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]) hsplit
  apply env_from_loop data (by constructor <;> simp [data, repeatedTypeSection,
    Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]) _
  rw [hstep]
  have hmore : ¬ 11#usize ≥ Slice.len data := by
    simp [data, repeatedTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  unfold parseLoop module.validate_env_with_loop
  rw [loop]
  simp [module.validate_env_with_loop.body, module.section_order, sectionRank, hmore, hheader, global_simps,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- A code section of size 0 has no room for its count, so the module is rejected with
`UnexpectedEof`, reported by the code framing of the streaming driver. -/
theorem truncated_code_count_rejected : module.validate_module (emptySection 10#u8) .Wasm1 =
    .ok (.Err .UnexpectedEof) := by
  let data := emptySection 10#u8
  let code := Examples.ModuleSupport.bytes [10#u8,0#u8]
  let empty := Examples.ModuleSupport.bytes []
  let regions : stream.SliceSource := ⟨Examples.ModuleBasic.emptyBytes, code, empty⟩
  have hsplit : StreamCompleteRegions.Split data regions := by
    refine ⟨8#usize, 10#usize, ?_, ?_, ?_, ?_⟩
    · rw [stream.find_code_region, stream.find_code_region_loop, loop,
        split_body_section data 8#usize 10#usize 10#usize 10#u8
          (empty_section_header 10#u8) (by decide)]
      simp
    all_goals simp [regions, code, empty, data, emptySection, Examples.ModuleBasic.emptyBytes,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      Slice.index_SliceIndexRangeUsizeSliceInst, core.slice.index.SliceIndexRangeUsizeSlice.index,
      List.slice]
  apply StreamSliceRejection.code_header_error data regions Examples.ModuleBasic.emptyEnv .UnexpectedEof
    (by simp [data, emptySection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]) hsplit Examples.ModuleBasic.empty_env
  have hview : stream.read_exact stream.SliceSource.Insts.ItascaStreamSource regions 0#usize 2#usize =
      .ok (.Ok code) := by
    obtain ⟨view, hr, hv⟩ := (stream.SliceSource.available regions).code_read
      0#usize 2#usize (by decide) (by rfl)
    have he : view = code := by
      apply Slice.ext
      simpa [regions, code, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, List.slice] using hv
    subst view
    exact stream.read_exact.complete _ _ _ _ _ (by decide) hr rfl
  have hzero : stream.read_len code 1#usize = .ok (.Ok (0#usize, 2#usize)) := by
    have hd : Leb128.Decoded code 1#usize 0#u32 2#usize :=
      (show Wasm1.BytesAt code 1#usize [0#u8] 2#usize from by
        constructor <;> simp [code, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]).u32_decoded _ (leb 0#u8)
    obtain ⟨n, hr, hn⟩ := stream.read_len.complete code 1#usize 2#usize 0#u32 hd
    have he : n = 0#usize := UScalar.eq_of_val_eq hn
    simpa [he] using hr
  have heof : stream.read_len code 2#usize = .ok (.Err .UnexpectedEof) := by
    have hr := reader.read_u32_leb.reject_complete code 2#usize .UnexpectedEof
      (.eof [] (by simp [code, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref]) (by simp) (by simp))
    simp [stream.read_len, hr]
  have hadd : limits.add_offset 2#usize 0#usize = .ok (.Ok 2#usize) := by
    obtain ⟨n, hr, hn⟩ := limits.add_offset.complete 2#usize 0#usize (by simp [limits.MAX_MODULE_BYTES])
    have he : n = 2#usize := by apply UScalar.eq_of_val_eq; simpa using hn
    simpa [he] using hr
  have hmin : core.cmp.impls.OrdUsize.min 2#usize 11#usize = 2#usize := by
    simp [core.cmp.impls.OrdUsize.min]
  have hlen : Slice.len regions.code = 2#usize := rfl
  have hs : stream.read_code_header stream.SliceSource.Insts.ItascaStreamSource
      regions (Slice.len regions.code) Examples.ModuleBasic.emptyEnv ⦃ r => r = .Err .UnexpectedEof ⦄ := by
    simp only [stream.read_code_header, hlen, show (2#usize ≠ 0#usize) by decide,
      ↓reduceIte, StreamFraming.header_limit, bind_ok, lift, hmin, hview,
      core.result.Result.Insts.CoreOpsTry.branch]
    step
    have hi : i2 = 10#u8 := by simpa [code, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref] using i2_post
    simp [hi, module.SECTION_CODE, hzero, hadd, heof,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

/-- A function section declaring one function of type 0 in a module with no types. -/
def invalidTypeIndex : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [3#u8,2#u8,1#u8,0#u8])
    (by simp [magicVersion]; scalar_tac)

/-- `invalidTypeIndex` is rejected with `UnknownType 0`. -/
theorem invalid_type_index_rejected : module.validate_module invalidTypeIndex .Wasm1 =
    .ok (.Err (.UnknownType 0#u32)) := by
  let data := invalidTypeIndex
  have hh : SectionHeader data 8#usize 3#u8 10#usize 12#usize := by
    apply section_header data 8#usize 9#usize 10#usize 12#usize 3#u8 2#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, invalidTypeIndex,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hc := (show At IndexEncoding data 10#usize 1#u32 11#usize from
    ⟨[1#u8], leb 1#u8, by constructor <;> simp [data, invalidTypeIndex,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have ht := (show At IndexEncoding data 11#usize 0#u32 12#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, invalidTypeIndex,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hd : module.decode_function_section data 10#usize Examples.ModuleBasic.emptyEnv =
      .ok (.Err (.UnknownType 0#u32), Examples.ModuleBasic.emptyEnv) := by
    simp [module.decode_function_section, hc, core.result.Result.Insts.CoreOpsTry.branch]
    unfold module.decode_function_section_loop
    rw [loop]
    simp [module.decode_function_section_loop.body, ht, module.lookup_type, lift,
      Examples.ModuleBasic.emptyEnv, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply first_section_error data (by constructor <;> simp [data, invalidTypeIndex, Examples.ModuleSupport.bytes,
    alloc.vec.Vec.deref, magicVersion]) 3#u8 10#usize 12#usize _ Examples.ModuleBasic.emptyEnv
    (by simp [data, invalidTypeIndex, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
    (by decide) (by decide) hh rfl
  · simpa [module.decode_env_section, global_simps] using hd
  · simp [data, invalidTypeIndex, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]

/-- A type section of declared size 2 holding only the empty vector count `00`. -/
def longEmptyTypeSection : Slice U8 :=
  Examples.ModuleSupport.bytes (magicVersion ++ [1#u8,2#u8,0#u8,0#u8])
    (by simp [magicVersion]; scalar_tac)

/-- The declared payload is available, but the empty type vector consumes one byte less than the
section size, so the module is rejected with `SectionSizeMismatch` rather than skipping the
extra byte. -/
theorem section_size_mismatch_rejected : module.validate_module longEmptyTypeSection .Wasm1 =
    .ok (.Err .SectionSizeMismatch) := by
  let data := longEmptyTypeSection
  have hh : SectionHeader data 8#usize 1#u8 10#usize 12#usize := by
    apply section_header data 8#usize 9#usize 10#usize 12#usize 1#u8 2#u8 (by decide)
    all_goals first | rfl | (apply Wasm1.BytesAt.mk <;> simp [data, longEmptyTypeSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hheader := module.read_section_header.complete data 8#usize 1#u8 10#usize 12#usize hh
  have hc := (show At IndexEncoding data 10#usize 0#u32 11#usize from
    ⟨[0#u8], leb 0#u8, by constructor <;> simp [data, longEmptyTypeSection,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]⟩).read_index
  have hd : module.decode_type_section data 10#usize Examples.ModuleBasic.emptyEnv .Wasm1 =
      .ok (.Ok 11#usize, Examples.ModuleBasic.emptyEnv) := by
    simp [module.decode_type_section, hc, core.result.Result.Insts.CoreOpsTry.branch]
    unfold module.decode_type_section_loop
    rw [loop]
    simp [module.decode_type_section_loop.body]
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize 10#usize 12#usize 1#u8 hh (by decide)]
    exact split_loop_eof data
  apply Examples.ModuleBasic.environment_error data _
    (by simp [data, longEmptyTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion,
      limits.MAX_MODULE_BYTES]) hsplit
  apply env_from_loop data (by constructor <;> simp [data, longEmptyTypeSection,
    Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]) _
  have hmore : ¬ 8#usize ≥ Slice.len data := by
    simp [data, longEmptyTypeSection, Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  unfold parseLoop module.validate_env_with_loop
  rw [loop]
  simp [module.validate_env_with_loop.body, module.section_order, hmore, hheader, module.decode_env_section, hd,
    global_simps, core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Examples.ModuleNegative
