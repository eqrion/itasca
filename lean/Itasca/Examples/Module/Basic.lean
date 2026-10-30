import Itasca.Main
import Itasca.Examples.Module.SliceLayout
import Itasca.Examples.Module.SliceRejection
import Itasca.Examples.Module.Support

/-!
# Header-only modules and header errors

The smallest whole modules. The eight-byte header `00 61 73 6d 01 00 00 00` alone is accepted by
`metadata.validate_module` and yields the empty environment (`empty_accepted`, `empty_validated`).
Empty input, a bad magic word and a bad version are rejected with the matching error. The generic
lemmas `accepted_at_end`, `environment_error` and `header_error` reduce the public entry point to
`metadata.validate_env` for the other module examples.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.ModuleBasic

open ModuleSupport (bytes)

/-- A module environment with no types, imports, functions, tables, memories or globals. -/
def emptyEnv : metadata.Env where
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

/-- The decoded module for the header alone: `emptyEnv` and no function bodies. -/
def emptyModule : metadata.Module := ⟨emptyEnv, ⟨alloc.vec.Vec.new _⟩⟩

/-- The eight header bytes `00 61 73 6d 01 00 00 00`. -/
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
    metadata.read_header data = .ok (.Ok 8#usize) := by
  have h0 := read_at data 0#usize 1#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h4 := read_at data 4#usize 5#usize 1#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h5 := read_at data 5#usize 6#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h6 := read_at data 6#usize 7#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  have h7 := read_at data 7#usize 8#usize 0#u8 (by simp [hdata, ModuleBinary.magicVersion]) rfl (by simp [hdata, ModuleBinary.magicVersion])
  simp [metadata.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- `metadata.validate_env` on the header alone returns `emptyEnv` and consumed length 8. -/
theorem empty_env : metadata.validate_env emptyBytes .Wasm1 = .ok (.Ok (emptyEnv, 8#usize)) := by
  have hh := header emptyBytes [] (by simp [emptyBytes, bytes, alloc.vec.Vec.deref])
  simp [metadata.validate_env, metadata.validate_env_with, metadata.Env.new, hh,
    core.result.Result.Insts.CoreOpsTry.branch, emptyEnv]
  unfold metadata.validate_env_with_loop
  rw [loop]
  simp [metadata.validate_env_with_loop.body, emptyBytes, bytes,
    alloc.vec.Vec.deref, ModuleBinary.magicVersion]

/-- `metadata.validate_module` accepts the header-only module under Wasm 1.0. -/
theorem empty_accepted : metadata.validate_module emptyBytes .Wasm1 = .ok (.Ok emptyModule) := by
  apply StreamSliceExamplesSupport.accepted_at_end emptyBytes emptyEnv
    (by simp [emptyBytes, bytes, ModuleBinary.magicVersion, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) rfl
  have hlen : Slice.len emptyBytes = 8#usize := UScalar.eq_of_val_eq rfl
  simpa [hlen] using empty_env

/-- The accepted header-only module has a `ModuleSound.Validated` certificate for these bytes,
which covers the external metadata and the Wasm 1.0 restrictions. -/
theorem empty_validated : ModuleSound.Validated emptyBytes emptyModule :=
  metadata.validate_module.wasm_sound _ _ empty_accepted

/-- A module of acceptable size with no declared functions, whose environment consumes all the
bytes, is accepted with that environment and an empty tail. -/
theorem accepted_at_end (data : Slice U8) (env : metadata.Env)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hfuncs : env.func_type_indices.val = [])
    (henv : metadata.validate_env data .Wasm1 = .ok (.Ok (env, Slice.len data))) :
    metadata.validate_module data .Wasm1 = .ok (.Ok ⟨env, ⟨alloc.vec.Vec.new _⟩⟩) :=
  StreamSliceExamplesSupport.accepted_at_end data env hsize hfuncs henv

/-- An error from `metadata.validate_env` is the result of `metadata.validate_module` when the code
region split is empty. -/
theorem environment_error (data : Slice U8) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data))
    (herror : metadata.validate_env data .Wasm1 = .ok (.Err e)) :
    metadata.validate_module data .Wasm1 = .ok (.Err e) :=
  StreamSliceRejection.environment_error data e hsize hsplit herror

/-- A header error on input of at most 8 bytes is the result of `metadata.validate_module`. -/
theorem header_error (data : Slice U8) (e : error.Error)
    (hsize : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (hshort : data.length ≤ 8)
    (herror : metadata.read_header data = .ok (.Err e)) :
    metadata.validate_module data .Wasm1 = .ok (.Err e) := by
  have hsplit : stream.find_code_region data = .ok (Slice.len data, Slice.len data) := by
    rw [stream.find_code_region, stream.find_code_region_loop, loop]
    have hstop : 8#usize ≥ Slice.len data := by scalar_tac
    simp [stream.find_code_region_loop.body, hstop]
  apply environment_error data e hsize hsplit
  simp [metadata.validate_env, metadata.validate_env_with, metadata.Env.new, herror,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Empty input is rejected with `UnexpectedEof`. -/
theorem missing_header_rejected : metadata.validate_module (bytes []) .Wasm1 =
    .ok (.Err (.Read .UnexpectedEof)) := by
  apply header_error _ _ (by simp [bytes, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) (by decide)
  simp [metadata.read_header, reader.read_byte.eof (bytes []) 0#usize (by simp [bytes, alloc.vec.Vec.deref]),
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    error.Error.Insts.CoreConvertFromOpError.from]

/-- A first byte of `01` instead of `00` in the magic word is rejected with `InvalidMagic`. -/
theorem invalid_magic_rejected : metadata.validate_module (bytes [1#u8, 0x61#u8, 0x73#u8, 0x6D#u8]) .Wasm1 =
    .ok (.Err .InvalidMagic) := by
  let data := bytes [1#u8, 0x61#u8, 0x73#u8, 0x6D#u8]
  have h0 := read_at data 0#usize 1#usize 1#u8 (by decide) rfl rfl
  have h1 := read_at data 1#usize 2#usize 0x61#u8 (by decide) rfl rfl
  have h2 := read_at data 2#usize 3#usize 0x73#u8 (by decide) rfl rfl
  have h3 := read_at data 3#usize 4#usize 0x6D#u8 (by decide) rfl rfl
  apply header_error data _ (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_MODULE_BYTES]) (by decide)
  simp [metadata.read_header, h0, h1, h2, h3, core.result.Result.Insts.CoreOpsTry.branch]

/-- The version `01 00 00 01` is rejected under Wasm 1.0 with `InvalidVersion`. -/
theorem invalid_version_rejected : metadata.validate_module
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
  simp [metadata.read_header, h0, h1, h2, h3, h4, h5, h6, h7,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.Examples.ModuleBasic
