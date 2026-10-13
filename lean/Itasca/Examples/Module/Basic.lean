import Itasca.Module.Validation
import Itasca.Stream.SliceLayout
import Itasca.Stream.SliceRejection

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleBasic

/-- Concrete fixtures use ordinary bounded vectors, with no external evaluator. -/
def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

def emptyEnv : module.Env where
  types := alloc.vec.Vec.new _
  imports := alloc.vec.Vec.new _
  globals := alloc.vec.Vec.new _
  exports := alloc.vec.Vec.new _
  elements := alloc.vec.Vec.new _
  start := none
  data_count := none
  declared_funcs := alloc.vec.Vec.new _
  func_type_indices := alloc.vec.Vec.new _
  func_types := alloc.vec.Vec.new _
  table_types := alloc.vec.Vec.new _
  mem_types := alloc.vec.Vec.new _
  global_types := alloc.vec.Vec.new _
  num_imported_funcs := 0#usize
  num_imported_globals := 0#usize

def emptyModule : module.Module := ⟨emptyEnv, ⟨alloc.vec.Vec.new _⟩⟩

def emptyBytes : Slice U8 := bytes ModuleBinary.magicVersion (by
  simp [ModuleBinary.magicVersion]; scalar_tac)

private theorem read_at (data : Slice U8) (pos next : Usize) (byte : U8)
    (hp : pos.val < data.length) (hn : next.val = pos.val + 1)
    (hb : data.val[pos.val] = byte) :
    reader.read_byte data pos = .ok (.Ok (byte, next)) := by
  obtain ⟨_, hr, p, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data pos hp)
  have he : p = next := UScalar.eq_of_val_eq (hnext.trans hn.symm)
  simpa [he, hb] using hr

/-- The fixed eight-byte header is accepted wherever its complete prefix occurs. -/
theorem header (data : Slice U8) (rest : List U8)
    (hdata : data.val = ModuleBinary.magicVersion ++ rest) :
    module.read_header data = .ok (.Ok 8#usize) := by
  have h0 := read_at data 0#usize 1#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h4 := read_at data 4#usize 5#usize 1#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h5 := read_at data 5#usize 6#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h6 := read_at data 6#usize 7#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h7 := read_at data 7#usize 8#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  simp [module.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem empty_env : module.validate_env emptyBytes .Wasm1 = .ok (.Ok (emptyEnv, 8#usize)) := by
  have hh := header emptyBytes [] (by simp [emptyBytes, bytes, alloc.vec.Vec.deref])
  simp [module.validate_env, module.validate_env_with, module.Env.new, hh,
    core.result.Result.Insts.CoreOpsTry.branch, emptyEnv]
  unfold module.validate_env_with_loop
  rw [loop]
  simp [module.validate_env_with_loop.body, emptyBytes, bytes,
    alloc.vec.Vec.deref, ModuleBinary.magicVersion]

/-- A header-only module is accepted by the actual public validator. -/
theorem empty_accepted : module.validate_module emptyBytes .Wasm1 = .ok (.Ok emptyModule) := by
  apply StreamSliceExamplesSupport.accepted_at_end emptyBytes emptyEnv
    (by simp [emptyBytes, bytes, ModuleBinary.magicVersion, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) rfl
  have hlen : Slice.len emptyBytes = 8#usize := UScalar.eq_of_val_eq rfl
  simpa [hlen] using empty_env

/-- Acceptance provides a certificate for these exact bytes, including external
metadata and the explicit Wasm 1.0 restrictions. -/
theorem empty_validated : ModuleSound.Validated emptyBytes emptyModule :=
  module.validate_module.wasm_sound _ _ empty_accepted

/-- With no declared functions and no remaining bytes, the synchronous
streaming driver returns the exact decoded environment and empty tail. -/
theorem accepted_at_end (data : Slice U8) (env : module.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hfuncs : env.func_type_indices.val = [])
    (henv : module.validate_env data .Wasm1 = .ok (.Ok (env, Slice.len data))) :
    module.validate_module data .Wasm1 = .ok (.Ok ⟨env, ⟨alloc.vec.Vec.new _⟩⟩) :=
  StreamSliceExamplesSupport.accepted_at_end data env hsize hfuncs henv

theorem environment_error (data : Slice U8) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data))
    (herror : module.validate_env data .Wasm1 = .ok (.Err e)) :
    module.validate_module data .Wasm1 = .ok (.Err e) :=
  StreamSliceRejection.environment_error data e hsize hsplit herror

theorem header_error (data : Slice U8) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hshort : data.length ≤ 8)
    (herror : module.read_header data = .ok (.Err e)) :
    module.validate_module data .Wasm1 = .ok (.Err e) := by
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    rw [stream.find_code_region, stream.find_code_region_loop, loop]
    have hstop : 8#usize ≥ Slice.len data := by scalar_tac
    simp [stream.find_code_region_loop.body, hstop]
  apply environment_error data e hsize hsplit
  simp [module.validate_env, module.validate_env_with, module.Env.new, herror,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Empty input is an ordinary EOF error at the public module entry point. -/
theorem missing_header_rejected : module.validate_module (bytes []) .Wasm1 =
    .ok (.Err (.Read .UnexpectedEof)) := by
  apply header_error _ _ (by simp [bytes, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) (by decide)
  simp [module.read_header, reader.read_byte.eof (bytes []) 0#usize (by simp [bytes, alloc.vec.Vec.deref]),
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    error.Error.Insts.CoreConvertFromOpError.from]

/-- A header with a non-Wasm magic word is rejected before version decoding. -/
theorem invalid_magic_rejected : module.validate_module (bytes [1#u8, 0x61#u8, 0x73#u8, 0x6D#u8]) .Wasm1 =
    .ok (.Err .InvalidMagic) := by
  let data := bytes [1#u8, 0x61#u8, 0x73#u8, 0x6D#u8]
  have h0 := read_at data 0#usize 1#usize 1#u8 (by decide) rfl rfl
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by decide) rfl rfl
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by decide) rfl rfl
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by decide) rfl rfl
  apply header_error data _ (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) (by decide)
  simp [module.read_header, h0, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch]

/-- Nonzero version padding cannot be mistaken for an accepted 1.0 header. -/
theorem invalid_version_rejected : module.validate_module
    (bytes [0#u8, 0x61#u8, 0x73#u8, 0x6D#u8, 1#u8, 0#u8, 0#u8, 1#u8]) .Wasm1 =
    .ok (.Err .InvalidVersion) := by
  let data := bytes [0#u8, 0x61#u8, 0x73#u8, 0x6D#u8, 1#u8, 0#u8, 0#u8, 1#u8]
  have h0 := read_at data 0#usize 1#usize 0#u8 (by decide) rfl rfl
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by decide) rfl rfl
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by decide) rfl rfl
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by decide) rfl rfl
  have h4 := read_at data 4#usize 5#usize 1#u8 (by decide) rfl rfl
  have h5 := read_at data 5#usize 6#usize 0#u8 (by decide) rfl rfl
  have h6 := read_at data 6#usize 7#usize 0#u8 (by decide) rfl rfl
  have h7 := read_at data 7#usize 8#usize 1#u8 (by decide) rfl rfl
  apply header_error data _ (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) (by decide)
  simp [module.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Examples.ModuleBasic
