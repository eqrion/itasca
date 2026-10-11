import Itasca.Module.ModuleCustomTrace
import Itasca.Module.ModuleTraceRecorders
import Itasca.Examples.ModuleUnicodeExamples

open Aeneas Aeneas.Std

namespace Itasca.ModuleTraceExamples

open ModuleTrace ModuleBinary

/-- The valid four-byte UTF-8 name occupies bytes 11 through 14. Its custom
payload is empty and the environment callback records its exact range. -/
def unicodeInput := ModuleUnicodeExamples.fourByteCustom 0xF4#u8 0x8F#u8 0xBF#u8 0xBF#u8

def unicodeChunk : types.CustomSection := ⟨4#usize, 15#usize, 15#usize⟩

def unicodeEvents : List Event := [.custom unicodeChunk]

private theorem leb (b : U8) (h : b.val < 128 := by decide) : Leb128.Encoding [b] b.val :=
  ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

private theorem unicode_length : Slice.len unicodeInput = 15#usize := UScalar.eq_of_val_eq rfl

private theorem unicode_environment : module.validate_env_with customRecorder unicodeInput .Wasm1 [] =
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

/-- Exact component callback execution for a custom section named U+10FFFF. -/
theorem unicode_recorded : module.validate_env_with customRecorder unicodeInput .Wasm1 [] =
    .ok (.Ok (ModuleExamples.emptyEnv, 15#usize), unicodeEvents) := unicode_environment

/-- The custom callback has independent section/name provenance, and the same
fixture is accepted by the synchronous streaming module validator. -/
theorem unicode_trace_validated : EnvTrace unicodeInput 15#usize unicodeEvents ∧
    ModuleSound.Validated unicodeInput ModuleExamples.emptyModule := by
  obtain ⟨events, he, ht⟩ := module.validate_env_with.accepted_trace
    customRecorder id customRecorder_records unicodeInput [] ModuleExamples.emptyEnv 15#usize
    unicodeEvents unicode_recorded
  have he : unicodeEvents = events := by simpa using he
  exact ⟨he ▸ ht, ModuleUnicodeExamples.last_scalar_module_validated⟩

end Itasca.ModuleTraceExamples
