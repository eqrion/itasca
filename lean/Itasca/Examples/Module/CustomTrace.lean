import Itasca.Module.Custom.Trace
import Itasca.Examples.Module.Unicode
import Itasca.Examples.Module.Support

/-!
# Custom-section callback trace

Runs `metadata.validate_env_with` with the recording visitor `customRecorder` on a module whose
only section is a custom section named U+10FFFF. `unicode_recorded` computes the exact callback
trace, and `unicode_trace_validated` shows that the trace is an `EnvTrace` of the input bytes and
that the same module is accepted with a soundness certificate.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleCustomTrace

open ModuleSupport (leb)

open ModuleTrace ModuleBinary

/-- A 15-byte module whose only section is a custom section with the four-byte UTF-8 name U+10FFFF
(bytes 11 to 14) and an empty payload. -/
def unicodeInput := Examples.ModuleUnicode.fourByteCustom 0xF4#u8 0x8F#u8 0xBF#u8 0xBF#u8

/-- The custom-section callback argument for `unicodeInput`: name length 4, empty payload at
offset 15. -/
def unicodeChunk : wasm_types.CustomSection := ⟨4#usize, 15#usize, 15#usize⟩

/-- The trace with the single custom-section event. -/
def unicodeEvents : List Event := [.custom unicodeChunk]

private theorem unicode_length : Slice.len unicodeInput = 15#usize := UScalar.eq_of_val_eq rfl

private theorem unicode_environment : metadata.validate_env_with customRecorder unicodeInput .Wasm1 [] =
    .ok (.Ok (Examples.ModuleBasic.emptyEnv, 15#usize), [.custom unicodeChunk]) := by
  let nm := alloc.vec.Vec.from [0xF4#u8, 0x8F#u8, 0xBF#u8, 0xBF#u8] (by simp; scalar_tac)
  have hheader := metadata.read_header.complete unicodeInput 8#usize (by
    constructor <;> simp [unicodeInput, Examples.ModuleUnicode.fourByteCustom,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion])
  have hsection : SectionHeader unicodeInput 8#usize 0#u8 10#usize 15#usize := by
    refine ⟨9#usize, 5#u32, ⟨[0#u8], rfl, ?_⟩, ?_, rfl, by decide⟩
    · constructor <;> simp [unicodeInput, Examples.ModuleUnicode.fourByteCustom,
        Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
    · refine ⟨[5#u8], ?_, rfl, ?_, leb 5#u8⟩ <;>
        simp [unicodeInput, Examples.ModuleUnicode.fourByteCustom,
          Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hread := metadata.read_section_header.complete unicodeInput 8#usize 0#u8 10#usize 15#usize hsection
  have hnamebytes : At ByteVecEncoding unicodeInput 10#usize nm.val 15#usize := by
    refine ⟨[4#u8,0xF4#u8,0x8F#u8,0xBF#u8,0xBF#u8],
      ByteVecEncoding.iff.mpr ⟨[4#u8], leb 4#u8, rfl⟩, ?_⟩
    constructor <;> simp [unicodeInput, Examples.ModuleUnicode.fourByteCustom,
      Examples.ModuleSupport.bytes, alloc.vec.Vec.deref, magicVersion]
  have hname := metadata.decode_name.from_utf8 unicodeInput 10#usize nm 15#usize hnamebytes
    (.Ok ()) Examples.ModuleUnicode.last_scalar_accepted
  have hn : alloc.vec.Vec.len nm = 4#usize := UScalar.eq_of_val_eq rfl
  simp [metadata.validate_env_with, metadata.Env.new, hheader,
    core.result.Result.Insts.CoreOpsTry.branch, Examples.ModuleBasic.emptyEnv]
  unfold metadata.validate_env_with_loop
  rw [loop]
  simp only [metadata.validate_env_with_loop.body, unicode_length,
    show (8#usize ≥ 15#usize) = False from by decide, ↓reduceIte,
    hread, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, metadata.SECTION_CUSTOM]
  simp [metadata.decode_custom_section, hname, hn, unicodeChunk,
    core.result.Result.Insts.CoreOpsTry.branch, customRecorder]
  rw [loop]
  simp

/-- `metadata.validate_env_with` with `customRecorder` on `unicodeInput` returns the empty
environment, consumed length 15 and the trace `unicodeEvents`. -/
theorem unicode_recorded : metadata.validate_env_with customRecorder unicodeInput .Wasm1 [] =
    .ok (.Ok (Examples.ModuleBasic.emptyEnv, 15#usize), unicodeEvents) := unicode_environment

/-- The recorded trace is an `EnvTrace` of `unicodeInput`, tying the callback to its section and
name bytes, and `unicodeInput` is accepted by `metadata.validate_module`. -/
theorem unicode_trace_validated : EnvTrace unicodeInput 15#usize unicodeEvents ∧
    ModuleSound.Validated unicodeInput Examples.ModuleBasic.emptyModule := by
  obtain ⟨events, he, ht⟩ := metadata.validate_env_with.accepted_trace
    customRecorder id customRecorder_records unicodeInput [] Examples.ModuleBasic.emptyEnv 15#usize
    unicodeEvents unicode_recorded
  have he : unicodeEvents = events := by simpa using he
  exact ⟨he ▸ ht, Examples.ModuleUnicode.last_scalar_module_validated⟩

end Itasca.Examples.ModuleCustomTrace
