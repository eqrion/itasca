import Itasca.ModuleEnvSemantics
import Itasca.ModuleValidation
import Itasca.ModuleExamples
import Itasca.ModuleNamesComplete

open Aeneas Aeneas.Std

namespace Itasca.ModuleUnicodeExamples

def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

/-- U+10FFFF is the largest Unicode scalar and exercises the corrected
four-byte upper bound in the generated specification. -/
def lastScalar : Slice U8 := bytes [0xF4#u8, 0x8F#u8, 0xBF#u8, 0xBF#u8]

theorem last_scalar_sequence : module.utf8_sequence_len lastScalar 0#usize = .ok (.Ok 4#usize) := by
  have hs : module.utf8_sequence_len lastScalar 0#usize ⦃ r => r = .Ok 4#usize ⦄ := by
    have hmax : 4 ≤ Usize.max := by scalar_tac
    simp only [lastScalar, bytes, alloc.vec.Vec.deref]
    unfold module.utf8_sequence_len module.utf8_cont
    step
    simp_all
    iterate 8
      all_goals step*
      all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr


def surrogate : Slice U8 := bytes [0xED#u8, 0xA0#u8, 0x80#u8]
def beyondUnicode : Slice U8 := bytes [0xF4#u8, 0x90#u8, 0x80#u8, 0x80#u8]

theorem surrogate_sequence_rejected : module.utf8_sequence_len surrogate 0#usize =
    .ok (.Err .InvalidUtf8) := by
  have hs : module.utf8_sequence_len surrogate 0#usize ⦃ r => r = .Err .InvalidUtf8 ⦄ := by
    have hmax : 4 ≤ Usize.max := by scalar_tac
    simp only [surrogate, bytes, alloc.vec.Vec.deref]
    unfold module.utf8_sequence_len module.utf8_cont
    step
    simp_all
    iterate 4
      all_goals step*
      all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

theorem beyond_unicode_sequence_rejected : module.utf8_sequence_len beyondUnicode 0#usize =
    .ok (.Err .InvalidUtf8) := by
  have hs : module.utf8_sequence_len beyondUnicode 0#usize ⦃ r => r = .Err .InvalidUtf8 ⦄ := by
    have hmax : 4 ≤ Usize.max := by scalar_tac
    simp only [beyondUnicode, bytes, alloc.vec.Vec.deref]
    unfold module.utf8_sequence_len module.utf8_cont
    step
    simp_all
    iterate 4
      all_goals step*
      all_goals simp_all [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists hs
  exact hr

private theorem utf8_reject (data : Slice U8) (h : 0 < data.length)
    (hr : module.utf8_sequence_len data 0#usize = .ok (.Err .InvalidUtf8)) :
    module.validate_utf8 data = .ok (.Err .InvalidUtf8) := by
  have hb : ¬ 0#usize ≥ data.len := by scalar_tac
  unfold module.validate_utf8 module.validate_utf8_loop
  rw [loop]
  simp [module.validate_utf8_loop.body, hb, hr,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem surrogate_rejected : module.validate_utf8 surrogate = .ok (.Err .InvalidUtf8) :=
  utf8_reject surrogate (by decide) surrogate_sequence_rejected

theorem beyond_unicode_rejected : module.validate_utf8 beyondUnicode = .ok (.Err .InvalidUtf8) :=
  utf8_reject beyondUnicode (by decide) beyond_unicode_sequence_rejected

theorem last_scalar_accepted : module.validate_utf8 lastScalar = .ok (.Ok ()) := by
  have hnext : (0#usize + 4#usize : Result Usize) = .ok 4#usize := by
    have hs : (0#usize + 4#usize) ⦃ r => r = 4#usize ⦄ := by step*
    obtain ⟨_, hr, rfl⟩ := WP.spec_imp_exists hs
    exact hr
  have hb : ¬ 0#usize ≥ lastScalar.len := by decide
  unfold module.validate_utf8 module.validate_utf8_loop
  rw [loop]
  simp only [module.validate_utf8_loop.body, hb, ↓reduceIte, last_scalar_sequence,
    bind_ok, core.result.Result.Insts.CoreOpsTry.branch, hnext]
  rw [loop]
  simp [lastScalar, bytes, alloc.vec.Vec.deref]

theorem last_scalar_name : ModuleBinary.nameOfBytes lastScalar.val =
    «name».mk_name [.mk_char 0x10FFFF] := by rfl


def fourByteCustom (a b c d : U8) : Slice U8 :=
  bytes (ModuleBinary.magicVersion ++ [0#u8, 5#u8, 4#u8, a, b, c, d])
    (by simp [ModuleBinary.magicVersion]; scalar_tac)

private theorem small_leb (b : U8) (h : b.val < 128) : Leb128.Encoding [b] b.val := by
  exact ⟨[], b, rfl, by simp, by simp, h, by simp, by simp [Leb128.payload, Nat.mod_eq_of_lt h]⟩

/-- The public module API preserves the exact UTF-8 reply of a four-byte custom
section name; successful callbacks leave the otherwise empty module unchanged. -/
private theorem four_byte_custom_reply (a b c d : U8) (reply : core.result.Result Unit error.Error)
    (hutf8 : module.validate_utf8 (bytes [a,b,c,d]) = .ok reply) :
    module.validate_module (fourByteCustom a b c d) = .ok (match reply with
      | .Ok _ => .Ok ModuleExamples.emptyModule
      | .Err e => .Err e) := by
  let data := fourByteCustom a b c d
  let nm := alloc.vec.Vec.from [a,b,c,d] (by simp; scalar_tac)
  have hlen : Slice.len data = 15#usize := UScalar.eq_of_val_eq rfl
  have hheader := module.read_header.complete data 8#usize
    (by constructor <;> simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion])
  have hsection : ModuleBinary.SectionHeader data 8#usize 0#u8 10#usize 15#usize := by
    refine ⟨9#usize, 5#u32, ⟨[0#u8], rfl, ?_⟩, ?_, rfl, by simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion]⟩
    · constructor <;> simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion]
    · refine ⟨[5#u8], ?_, rfl, ?_, small_leb 5#u8 (by decide)⟩ <;>
        simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion]
  have hread := module.read_section_header.complete data 8#usize 0#u8 10#usize 15#usize hsection
  have hnamebytes : ModuleBinary.At ModuleBinary.ByteVecEncoding data 10#usize nm.val 15#usize := by
    refine ⟨[4#u8,a,b,c,d], ModuleBinary.ByteVecEncoding.iff.mpr ⟨[4#u8], small_leb 4#u8 (by decide), rfl⟩, ?_⟩
    constructor <;> simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion]
  have hname := module.decode_name.from_utf8 data 10#usize nm 15#usize hnamebytes reply hutf8
  have henv : module.validate_env data = .ok (match reply with
      | .Ok _ => .Ok (ModuleExamples.emptyEnv, 15#usize)
      | .Err e => .Err e) := by
    simp [module.validate_env, module.validate_env_with, module.Env.new, hheader,
      core.result.Result.Insts.CoreOpsTry.branch, ModuleExamples.emptyEnv]
    unfold module.validate_env_with_loop
    rw [loop]
    simp only [module.validate_env_with_loop.body, hlen,
      show (8#usize ≥ 15#usize) = False from by decide, ↓reduceIte,
      hread, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, module.SECTION_CUSTOM]
    cases reply with
    | Err e =>
        simp [module.decode_custom_section, hname,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
        simp [module.decode_custom_section, hname,
          core.result.Result.Insts.CoreOpsTry.branch,
          module.ModuleVisitor.on_custom_section.default]
        rw [loop]
        simp
  have hsize : data.length ≤ limits.MAX_MODULE_BYTES.val := by
    simp [data, fourByteCustom, bytes, alloc.vec.Vec.deref, ModuleBinary.magicVersion, limits.MAX_MODULE_BYTES]
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    unfold stream.find_code_region
    rw [split_skip_section data 8#usize 10#usize 15#usize 0#u8 hsection (by decide)]
    simpa [hlen] using split_loop_eof data
  cases reply with
  | Err e => exact ModuleExamples.environment_error data e hsize hsplit henv
  | Ok u =>
      exact ModuleExamples.accepted_at_end data ModuleExamples.emptyEnv hsize rfl (by simpa [hlen] using henv)

theorem last_scalar_module_accepted :
    module.validate_module (fourByteCustom 0xF4#u8 0x8F#u8 0xBF#u8 0xBF#u8) =
      .ok (.Ok ModuleExamples.emptyModule) :=
  four_byte_custom_reply _ _ _ _ (.Ok ()) last_scalar_accepted

theorem last_scalar_module_validated :
    ModuleSound.Validated (fourByteCustom 0xF4#u8 0x8F#u8 0xBF#u8 0xBF#u8) ModuleExamples.emptyModule :=
  module.validate_module.wasm_sound _ _ last_scalar_module_accepted

theorem beyond_unicode_module_rejected :
    module.validate_module (fourByteCustom 0xF4#u8 0x90#u8 0x80#u8 0x80#u8) =
      .ok (.Err .InvalidUtf8) :=
  four_byte_custom_reply _ _ _ _ (.Err .InvalidUtf8) beyond_unicode_rejected

end Itasca.ModuleUnicodeExamples
