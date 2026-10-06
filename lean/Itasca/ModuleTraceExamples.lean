import Itasca.ModuleTraceValidation
import Itasca.ModuleUnicodeExamples

open Aeneas Aeneas.Std

namespace Itasca.ModuleTraceExamples

open ModuleTrace ModuleBinary

/-- The valid four-byte UTF-8 name occupies bytes 11 through 14. Its custom
payload is empty, and code framing still requests eleven bytes beyond EOF. -/
def unicodeInput := ModuleUnicodeExamples.fourByteCustom 0xF4#u8 0x8F#u8 0xBF#u8 0xBF#u8

def unicodeChunk : types.CustomSection := ⟨4#usize, 15#usize, 15#usize⟩

def unicodeEvents : List Event := [.custom unicodeChunk, .needBytes 26#usize]

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem header_limit : limits.MAX_CODE_HEADER_BYTES = .ok 11#usize := by
  have hs : limits.MAX_CODE_HEADER_BYTES ⦃ n => n = 11#usize ⦄ := by
    unfold limits.MAX_CODE_HEADER_BYTES limits.MAX_LEB_BYTES
    step*
  obtain ⟨n, hn, rfl⟩ := WP.spec_imp_exists hs
  exact hn

private theorem add_eq (x y z : Usize) (h : z.val = x.val + y.val) :
    (x + y : Result Usize) = .ok z := by
  obtain ⟨n, hn, he⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := y) (by scalar_tac))
  have hz : n = z := UScalar.eq_of_val_eq (he.trans h.symm)
  simpa only [hz] using hn

private theorem unicode_length : Slice.len unicodeInput = 15#usize := UScalar.eq_of_val_eq rfl

private theorem unicode_environment : module.validate_env_with customRecorder unicodeInput [] =
    .ok (.Ok (ModuleExamples.emptyEnv, 15#usize), [.custom unicodeChunk]) := by
  let nm := alloc.vec.Vec.from [0xF4#u8, 0x8F#u8, 0xBF#u8, 0xBF#u8] (by simp; scalar_tac)
  have hheader := module.read_header.complete unicodeInput 8#usize (by
    constructor <;> simp [unicodeInput, ModuleUnicodeExamples.fourByteCustom,
      ModuleUnicodeExamples.bytes, alloc.vec.Vec.deref, magicVersion])
  have hsection : SectionHeader unicodeInput 8#usize 0#u8 10#usize 15#usize := by
    refine ⟨9#usize, 5#u32, ⟨[0#u8], rfl, ?_⟩, ?_, rfl, by decide⟩
    · constructor <;> simp [unicodeInput, ModuleUnicodeExamples.fourByteCustom,
        ModuleUnicodeExamples.bytes, alloc.vec.Vec.deref, magicVersion]
    · refine ⟨[5#u8], ?_, rfl, ?_, leb 5#u8⟩ <;>
        simp [unicodeInput, ModuleUnicodeExamples.fourByteCustom,
          ModuleUnicodeExamples.bytes, alloc.vec.Vec.deref, magicVersion]
  have hread := module.read_section_header.complete unicodeInput 8#usize 0#u8 10#usize 15#usize hsection
  have hnamebytes : At ByteVecEncoding unicodeInput 10#usize nm.val 15#usize := by
    refine ⟨[4#u8,0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8],
      ByteVecEncoding.iff.mpr ⟨[4#u8], leb 4#u8, rfl⟩, ?_⟩
    constructor <;> simp [unicodeInput, ModuleUnicodeExamples.fourByteCustom,
      ModuleUnicodeExamples.bytes, alloc.vec.Vec.deref, magicVersion]
  have hname := module.decode_name.from_utf8 unicodeInput 10#usize nm 15#usize hnamebytes
    (.Ok ()) ModuleUnicodeExamples.last_scalar_accepted
  have hn : alloc.vec.Vec.len nm = 4#usize := UScalar.eq_of_val_eq rfl
  simp [module.validate_env_with, module.Env.new, hheader,
    core.result.Result.Insts.CoreOpsTry.branch, ModuleExamples.emptyEnv]
  unfold module.validate_env_with_loop
  rw [loop]
  simp only [module.validate_env_with_loop.body, unicode_length,
    show (8#usize ≥ 15#usize) = False from by decide, ↓reduceIte,
    hread, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, module.SECTION_CUSTOM]
  simp [module.decode_custom_section, hname, hn, unicodeChunk,
    core.result.Result.Insts.CoreOpsTry.branch, customRecorder]
  rw [loop]
  simp

private theorem unicode_code : module.validate_code_with validatingRecorder unicodeInput 15#usize
    ModuleExamples.emptyEnv [.custom unicodeChunk] = .ok (.Ok 15#usize, unicodeEvents) := by
  apply ModuleCodeVisitor.SectionRun.accepted
  apply ModuleCodeVisitor.SectionRun.absent header_limit (add_eq 15#usize 11#usize 26#usize rfl)
    (by rfl)
  simp [module.code_section, unicode_length, module.no_code_section, ModuleExamples.emptyEnv,
    alloc.vec.Vec.is_empty]

private theorem unicode_tail : module.validate_tail_with customRecorder unicodeInput 15#usize
    ModuleExamples.emptyEnv unicodeEvents = .ok (.Ok ModuleExamples.emptyModule.tail, unicodeEvents) := by
  unfold module.validate_tail_with module.validate_tail_with_loop
  rw [loop]
  simp [module.validate_tail_with_loop.body, unicode_length, ModuleExamples.emptyModule]

/-- Exact public callback execution for a custom section named U+10FFFF. -/
theorem unicode_recorded : module.validate_module_with customRecorder validatingRecorder unicodeInput [] =
    .ok (.Ok ModuleExamples.emptyModule, unicodeEvents) := by
  apply ModulePipeline.accepted_of_parts_with customRecorder validatingRecorder unicodeInput
    ModuleExamples.emptyEnv ModuleExamples.emptyModule.tail 15#usize 15#usize []
    [.custom unicodeChunk] unicodeEvents unicodeEvents
  · simp [unicodeInput, ModuleUnicodeExamples.fourByteCustom, ModuleUnicodeExamples.bytes,
      alloc.vec.Vec.deref, magicVersion, limits.MAX_MODULE_BYTES]
  · exact unicode_environment
  · exact unicode_code
  · exact unicode_tail

/-- The same concrete callback list has independent section/name provenance
and belongs to the same semantically validated module. -/
theorem unicode_trace_validated : Accepted unicodeInput ModuleExamples.emptyModule unicodeEvents ∧
    ModuleSound.Validated unicodeInput ModuleExamples.emptyModule := by
  obtain ⟨events, he, ht, hs⟩ := module.validate_module_with.trace_sound
    customRecorder validatingRecorder id customRecorder_records validatingRecorder_records
    unicodeInput [] unicodeEvents ModuleExamples.emptyModule
    (validatingRecorder_validates unicodeInput ModuleExamples.emptyEnv) unicode_recorded
  have he : unicodeEvents = events := by simpa using he
  exact ⟨he ▸ ht, hs⟩

end Itasca.ModuleTraceExamples
