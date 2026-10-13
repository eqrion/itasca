import Itasca.Wasm1.Soundness
import Itasca.Handler.ScalarConst
import Itasca.Examples.Wasm1.Support

/-!
# Wasm 1.0 numeric constants

Bodies consisting of one `i64.const`, `f32.const` or `f64.const` followed by `end`, accepted by
`code.validate_body` and given `Wasm1.Validated` certificates, together with the translation of
their immediates to SpecTec floating-point values (`f32_negative_zero`, `f64_nan_payload`). Two
malformed immediates, a truncated `f64` and an over-long signed LEB128, are rejected with
`UnexpectedEof` and `LebTooLong`.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1Scalars

open Wasm1Support


/-- A context with no locals and the single result type `ty`. -/
def resultContext (ty : types.ValueType) : code.Context :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [ty] (by scalar_tac)⟩

/-- The body bytes `42 ff 7f 0b`: `i64.const -1` in a two-byte encoding, then `end`. -/
def i64Bytes : Slice U8 := bytes [0x42#u8, 0xFF#u8, 0x7F#u8, 0x0B#u8]
/-- The body bytes `43 00 00 00 80 0b`: `f32.const` with bits `0x80000000` (negative zero), then
`end`. -/
def f32Bytes : Slice U8 := bytes [0x43#u8, 0#u8, 0#u8, 0#u8, 0x80#u8, 0x0B#u8]
/-- The body bytes `44 01 00 00 00 00 00 f8 ff 0b`: `f64.const` with bits `0xfff8000000000001` (a
negative NaN with a payload), then `end`. -/
def f64Bytes : Slice U8 := bytes [0x44#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0xF8#u8, 0xFF#u8, 0x0B#u8]

/-- `code.validate_body` accepts `i64Bytes` with one `i64` result. -/
theorem i64_body_accepted (env : module.Env) :
    code.validate_body i64Bytes env (resultContext .I64) = .ok (.Ok ()) := by
  let initial := Wasm1.Loop.initial (.Value .I64)
  let first := { initial with pos := 1#usize }
  have hencoded : SignedLeb64.Decoded i64Bytes 1#usize ((-1)#i64).val 3#usize := by
    refine ⟨[0xFF#u8, 0x7F#u8], rfl, rfl, by decide, [0xFF#u8], 0x7F#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  have hleb := reader.read_s64_leb.complete i64Bytes 1#usize (-1)#i64 3#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_i64_const.from_read first i64Bytes (-1)#i64 3#usize hleb
      (by simp [first, initial, Wasm1.Loop.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 4#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .I64, Control.signature (.Value .I64), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Wasm1.Loop.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .I64)).map code.StackType.Val := by
    simpa [last, first, initial, Wasm1.Loop.initial, Control.results] using hv
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Value .I64, Control.signature (.Value .I64), 0#usize, false⟩ [] hctrls hvals rfl
      (by simp))
  dsimp only at hfc hfv hfp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first i64Bytes env
      (resultContext .I64) code.OP_I64_CONST () = .ok (.Ok (), pushed, ()) := by
    simp [global_simps, hconst, code.OpVisitor.on_i64_const.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop i64Bytes env (resultContext .I64) (.Value .I64) (.Ok ())
    (by simp [i64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step i64Bytes env (resultContext .I64) initial first pushed code.OP_I64_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at i64Bytes initial 1#usize code.OP_I64_CONST (by decide) rfl
      (by simp [i64Bytes, bytes, initial, Wasm1.Loop.initial, code.OP_I64_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step i64Bytes env (resultContext .I64) pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at i64Bytes pushed 4#usize code.OP_END (by simp [hp, i64Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, i64Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end i64Bytes env (resultContext .I64) last finished .Body (.Value .I64) hend)]
  exact loop_done i64Bytes env (resultContext .I64) finished hfc hfp

/-- The accepted `i64Bytes` body has a `Wasm1.Validated` certificate. -/
theorem i64_body_validated (env : module.Env) :
    Wasm1.Validated i64Bytes env (resultContext .I64) (.Value .I64) :=
  code.validate_body.wasm_sound i64Bytes env (resultContext .I64) (.Value .I64) rfl
    (i64_body_accepted env)

/-- `code.validate_body` accepts `f32Bytes` with one `f32` result. -/
theorem f32_body_accepted (env : module.Env) :
    code.validate_body f32Bytes env (resultContext .F32) = .ok (.Ok ()) := by
  let initial := Wasm1.Loop.initial (.Value .F32)
  let first := { initial with pos := 1#usize }
  have hencoded : FloatBits.Decoded 4 f32Bytes 1#usize (0x80000000#u32).val 5#usize := by
    refine ⟨[0#u8, 0#u8, 0#u8, 0x80#u8], rfl, rfl, by decide, rfl, ?_⟩
    norm_num [FloatBits.payload]
  have hleb := reader.read_f32_bits.complete f32Bytes 1#usize 0x80000000#u32 5#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_f32_const.from_read first f32Bytes 0x80000000#u32 5#usize hleb
      (by simp [first, initial, Wasm1.Loop.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 6#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .F32, Control.signature (.Value .F32), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Wasm1.Loop.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .F32)).map code.StackType.Val := by
    simpa [last, first, initial, Wasm1.Loop.initial, Control.results] using hv
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Value .F32, Control.signature (.Value .F32), 0#usize, false⟩ [] hctrls hvals rfl
      (by simp))
  dsimp only at hfc hfv hfp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first f32Bytes env
      (resultContext .F32) code.OP_F32_CONST () = .ok (.Ok (), pushed, ()) := by
    simp [global_simps, hconst, code.OpVisitor.on_f32_const.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop f32Bytes env (resultContext .F32) (.Value .F32) (.Ok ())
    (by simp [f32Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step f32Bytes env (resultContext .F32) initial first pushed code.OP_F32_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at f32Bytes initial 1#usize code.OP_F32_CONST (by decide) rfl
      (by simp [f32Bytes, bytes, initial, Wasm1.Loop.initial, code.OP_F32_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step f32Bytes env (resultContext .F32) pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at f32Bytes pushed 6#usize code.OP_END (by simp [hp, f32Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f32Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f32Bytes env (resultContext .F32) last finished .Body (.Value .F32) hend)]
  exact loop_done f32Bytes env (resultContext .F32) finished hfc hfp

/-- The accepted `f32Bytes` body has a `Wasm1.Validated` certificate. -/
theorem f32_body_validated (env : module.Env) :
    Wasm1.Validated f32Bytes env (resultContext .F32) (.Value .F32) :=
  code.validate_body.wasm_sound f32Bytes env (resultContext .F32) (.Value .F32) rfl
    (f32_body_accepted env)

/-- `code.validate_body` accepts `f64Bytes` with one `f64` result. -/
theorem f64_body_accepted (env : module.Env) :
    code.validate_body f64Bytes env (resultContext .F64) = .ok (.Ok ()) := by
  let initial := Wasm1.Loop.initial (.Value .F64)
  let first := { initial with pos := 1#usize }
  have hencoded : FloatBits.Decoded 8 f64Bytes 1#usize (0xFFF8000000000001#u64).val 9#usize := by
    refine ⟨[1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0xF8#u8, 0xFF#u8], rfl, rfl, by decide, rfl, ?_⟩
    norm_num [FloatBits.payload]
  have hleb := reader.read_f64_bits.complete f64Bytes 1#usize 0xFFF8000000000001#u64 9#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_f64_const.from_read first f64Bytes 0xFFF8000000000001#u64 9#usize hleb
      (by simp [first, initial, Wasm1.Loop.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 10#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .F64, Control.signature (.Value .F64), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Wasm1.Loop.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .F64)).map code.StackType.Val := by
    simpa [last, first, initial, Wasm1.Loop.initial, Control.results] using hv
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Value .F64, Control.signature (.Value .F64), 0#usize, false⟩ [] hctrls hvals rfl
      (by simp))
  dsimp only at hfc hfv hfp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first f64Bytes env
      (resultContext .F64) code.OP_F64_CONST () = .ok (.Ok (), pushed, ()) := by
    simp [global_simps, hconst, code.OpVisitor.on_f64_const.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop f64Bytes env (resultContext .F64) (.Value .F64) (.Ok ())
    (by simp [f64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step f64Bytes env (resultContext .F64) initial first pushed code.OP_F64_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at f64Bytes initial 1#usize code.OP_F64_CONST (by decide) rfl
      (by simp [f64Bytes, bytes, initial, Wasm1.Loop.initial, code.OP_F64_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step f64Bytes env (resultContext .F64) pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at f64Bytes pushed 10#usize code.OP_END (by simp [hp, f64Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f64Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f64Bytes env (resultContext .F64) last finished .Body (.Value .F64) hend)]
  exact loop_done f64Bytes env (resultContext .F64) finished hfc hfp

/-- The accepted `f64Bytes` body has a `Wasm1.Validated` certificate. -/
theorem f64_body_validated (env : module.Env) :
    Wasm1.Validated f64Bytes env (resultContext .F64) (.Value .F64) :=
  code.validate_body.wasm_sound f64Bytes env (resultContext .F64) (.Value .F64) rfl
    (f64_body_accepted env)

/-- The bits `0x80000000` translate to IEEE negative zero, which is distinct from positive zero. -/
theorem f32_negative_zero : ScalarConst.floatValue 23 8 (0x80000000#u32).val = .NEG (.SUBNORM 0) := by
  decide

/-- The bits `0xfff8000000000001` translate to a NaN that keeps its sign and nonzero payload. -/
theorem f64_nan_payload : ScalarConst.floatValue 52 11 (0xFFF8000000000001#u64).val =
    .NEG (.NAN 0x8000000000001) := by
  decide

/-- The body bytes `44` followed by seven zero bytes: an `f64.const` immediate one byte short. -/
def truncatedF64Bytes : Slice U8 := bytes [0x44#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
/-- The body bytes `42` followed by ten `80` bytes: an `i64.const` whose LEB128 immediate never
terminates within ten bytes. -/
def overlongI64Bytes : Slice U8 := bytes [0x42#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8,
  0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8, 0x80#u8]

private theorem truncated_f64_reader : reader.read_f64_bits truncatedF64Bytes 1#usize =
    .ok (.Err .UnexpectedEof) := by
  obtain ⟨res, hr, hp⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec truncatedF64Bytes 1#usize)
  cases res with
  | Err e => obtain ⟨rfl, _⟩ := hp; exact hr
  | Ok pair =>
    obtain ⟨bits, next⟩ := pair
    have hs := FloatBits.Decoded.span 8 truncatedF64Bytes 1#usize bits.val next hp
    norm_num [truncatedF64Bytes, bytes, alloc.vec.Vec.deref] at hs
    omega

private theorem overlong_i64_reader : reader.read_s64_leb overlongI64Bytes 1#usize =
    .ok (.Err .LebTooLong) := by
  obtain ⟨res, hr, hp⟩ := WP.spec_imp_exists (reader.read_s64_leb.spec overlongI64Bytes 1#usize)
  cases res with
  | Err e =>
    rcases SignedLeb64.Rejected.kind hp with he | he
    · subst e
      cases hp with
      | eof before hb hl _ =>
        change before.length ≤ 9 at hl
        have hlen := congrArg List.length hb
        norm_num [overlongI64Bytes, bytes, alloc.vec.Vec.deref] at hlen
        omega
    · simpa [he] using hr
  | Ok pair =>
    obtain ⟨value, next⟩ := pair
    obtain ⟨bs, hbytes, _, _, before, last, rfl, _, _, hlast, _⟩ := hp
    have hmem : last ∈ overlongI64Bytes.val.drop (1#usize).val := by rw [hbytes]; simp
    have heq : last = 0x80#u8 := by
      simpa [overlongI64Bytes, bytes, alloc.vec.Vec.deref] using hmem
    subst last
    norm_num at hlast

/-- `code.validate_body` rejects `truncatedF64Bytes` with `UnexpectedEof`. -/
theorem truncated_f64_body_rejected (env : module.Env) :
    code.validate_body truncatedF64Bytes env (resultContext .F64) = .ok (.Err .UnexpectedEof) := by
  let first := { Wasm1.Loop.initial (.Value .F64) with pos := 1#usize }
  have hread := code.read_f64_const.failed_read first truncatedF64Bytes .UnexpectedEof truncated_f64_reader
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first truncatedF64Bytes env
      (resultContext .F64) code.OP_F64_CONST () = .ok (.Err .UnexpectedEof, first, ()) := by
    simp [global_simps, hread, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop truncatedF64Bytes env (resultContext .F64) (.Value .F64) (.Err .UnexpectedEof)
    (by simp [truncatedF64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error truncatedF64Bytes env (resultContext .F64) (Wasm1.Loop.initial (.Value .F64)) first first
    code.OP_F64_CONST .UnexpectedEof (by simp [Wasm1.Loop.initial])
    (read_at truncatedF64Bytes (Wasm1.Loop.initial (.Value .F64)) 1#usize code.OP_F64_CONST (by decide) rfl
      (by simp [truncatedF64Bytes, bytes, Wasm1.Loop.initial, code.OP_F64_CONST, alloc.vec.Vec.deref])) hstep

/-- `code.validate_body` rejects `overlongI64Bytes` with `LebTooLong`, before the missing `end`
matters. -/
theorem overlong_i64_body_rejected (env : module.Env) :
    code.validate_body overlongI64Bytes env (resultContext .I64) = .ok (.Err .LebTooLong) := by
  let first := { Wasm1.Loop.initial (.Value .I64) with pos := 1#usize }
  have hread := code.read_i64_const.failed_read first overlongI64Bytes .LebTooLong overlong_i64_reader
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first overlongI64Bytes env
      (resultContext .I64) code.OP_I64_CONST () = .ok (.Err .LebTooLong, first, ()) := by
    simp [global_simps, hread, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop overlongI64Bytes env (resultContext .I64) (.Value .I64) (.Err .LebTooLong)
    (by simp [overlongI64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error overlongI64Bytes env (resultContext .I64) (Wasm1.Loop.initial (.Value .I64)) first first
    code.OP_I64_CONST .LebTooLong (by simp [Wasm1.Loop.initial])
    (read_at overlongI64Bytes (Wasm1.Loop.initial (.Value .I64)) 1#usize code.OP_I64_CONST (by decide) rfl
      (by simp [overlongI64Bytes, bytes, Wasm1.Loop.initial, code.OP_I64_CONST, alloc.vec.Vec.deref])) hstep

end Itasca.Examples.Wasm1Scalars
