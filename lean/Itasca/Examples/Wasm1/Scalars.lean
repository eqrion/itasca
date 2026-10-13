import Itasca.Wasm1.Soundness
import Itasca.Handler.ScalarConst

open Aeneas Aeneas.Std

namespace Itasca.WasmScalarExamples

private theorem public_of_loop (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (result : core.result.Result Unit error.OpError)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hresults : ctx.results.val = Control.results bt)
    (hloop : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () (Body.initial bt) = .ok (result, ())) :
    code.validate_body data env ctx = .ok result := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  simp [code.validate_body, code.validate_body_with.eq_model, code.validate_body_with_model, hguard,
    code.start_function.spec (alloc.vec.Vec.deref ctx.results) bt
      (by simpa [alloc.vec.Vec.deref] using hresults), hloop]

private theorem loop_done (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos = Slice.len data) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Ok (), ()) := by
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty, hc, hp]

private theorem loop_trailing (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st : code.OpIterState) (hc : st.ctrls.val = []) (hp : st.pos ≠ Slice.len data) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Err .TrailingBytes, ()) := by
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty, hc, hp]

private theorem loop_step (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Ok (), next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st =
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () next := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  conv_lhs => rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch]

private theorem loop_error (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st decoded next : code.OpIterState) (opcode : U8) (e : error.OpError) (hc : st.ctrls.val ≠ [])
    (hr : code.read_op st data = .ok (.Ok opcode, decoded))
    (hs : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor decoded data env ctx opcode () =
      .ok (.Err e, next, ())) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () st = .ok (.Err e, ()) := by
  have hempty : st.ctrls.val.isEmpty = false := by simpa using hc
  unfold code.validate_body_with_loop
  rw [loop]
  simp [code.validate_body_with_loop.body, code.control_stack_empty, alloc.vec.Vec.is_empty,
    hempty, hr, hs, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

private theorem read_at (data : Slice U8) (st : code.OpIterState) (next : Usize) (opcode : U8)
    (hp : st.pos.val < data.length) (hn : next.val = st.pos.val + 1)
    (hb : data.val[st.pos.val] = opcode) :
    code.read_op st data = .ok (.Ok opcode, {st with pos := next}) := by
  obtain ⟨q, hr, hq⟩ := code.read_op_success st data hp
  have heq : q = next := UScalar.eq_of_val_eq (hq.trans hn.symm)
  simpa [heq, hb] using hr

private theorem step_end (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st next : code.OpIterState) (kind : code.LabelKind) (bt : code.BlockType)
    (hr : code.read_end st = .ok (.Ok (kind, bt), next)) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx code.OP_END () =
      .ok (.Ok (), next, ()) := by
  simp [global_simps, hr,
    code.OpVisitor.on_end.default, code.visit, core.result.Result.Insts.CoreOpsTry.branch]


def bytes (xs : List U8) (h : xs.length ≤ Usize.max := by scalar_tac) : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from xs h)

def resultContext (ty : types.ValueType) : code.Context :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [ty] (by scalar_tac)⟩

def i64Bytes : Slice U8 := bytes [0x42#u8, 0xFF#u8, 0x7F#u8, 0x0B#u8]
def f32Bytes : Slice U8 := bytes [0x43#u8, 0#u8, 0#u8, 0#u8, 0x80#u8, 0x0B#u8]
def f64Bytes : Slice U8 := bytes [0x44#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0xF8#u8, 0xFF#u8, 0x0B#u8]

theorem i64_body_accepted (env : module.Env) :
    code.validate_body i64Bytes env (resultContext .I64) = .ok (.Ok ()) := by
  let initial := Body.initial (.Value .I64)
  let first := { initial with pos := 1#usize }
  have hencoded : SignedLeb64.Decoded i64Bytes 1#usize ((-1)#i64).val 3#usize := by
    refine ⟨[0xFF#u8, 0x7F#u8], rfl, rfl, by decide, [0xFF#u8], 0x7F#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb64.finalValue, Leb128.payload]
  have hleb := reader.read_s64_leb.complete i64Bytes 1#usize (-1)#i64 3#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_i64_const.from_read first i64Bytes (-1)#i64 3#usize hleb
      (by simp [first, initial, Body.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 4#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .I64, Control.signature (.Value .I64), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Body.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .I64)).map code.StackType.Val := by
    simpa [last, first, initial, Body.initial, Control.results] using hv
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
    (by simp [initial, Body.initial])
    (read_at i64Bytes initial 1#usize code.OP_I64_CONST (by decide) rfl
      (by simp [i64Bytes, bytes, initial, Body.initial, code.OP_I64_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step i64Bytes env (resultContext .I64) pushed last finished code.OP_END
    (by simp [hc, first, initial, Body.initial])
    (read_at i64Bytes pushed 4#usize code.OP_END (by simp [hp, i64Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, i64Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end i64Bytes env (resultContext .I64) last finished .Body (.Value .I64) hend)]
  exact loop_done i64Bytes env (resultContext .I64) finished hfc hfp

theorem i64_body_validated (env : module.Env) :
    Wasm.Validated i64Bytes env (resultContext .I64) (.Value .I64) :=
  code.validate_body.wasm_sound i64Bytes env (resultContext .I64) (.Value .I64) rfl
    (i64_body_accepted env)

theorem f32_body_accepted (env : module.Env) :
    code.validate_body f32Bytes env (resultContext .F32) = .ok (.Ok ()) := by
  let initial := Body.initial (.Value .F32)
  let first := { initial with pos := 1#usize }
  have hencoded : FloatBits.Decoded 4 f32Bytes 1#usize (0x80000000#u32).val 5#usize := by
    refine ⟨[0#u8, 0#u8, 0#u8, 0x80#u8], rfl, rfl, by decide, rfl, ?_⟩
    norm_num [FloatBits.payload]
  have hleb := reader.read_f32_bits.complete f32Bytes 1#usize 0x80000000#u32 5#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_f32_const.from_read first f32Bytes 0x80000000#u32 5#usize hleb
      (by simp [first, initial, Body.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 6#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .F32, Control.signature (.Value .F32), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Body.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .F32)).map code.StackType.Val := by
    simpa [last, first, initial, Body.initial, Control.results] using hv
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
    (by simp [initial, Body.initial])
    (read_at f32Bytes initial 1#usize code.OP_F32_CONST (by decide) rfl
      (by simp [f32Bytes, bytes, initial, Body.initial, code.OP_F32_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step f32Bytes env (resultContext .F32) pushed last finished code.OP_END
    (by simp [hc, first, initial, Body.initial])
    (read_at f32Bytes pushed 6#usize code.OP_END (by simp [hp, f32Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f32Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f32Bytes env (resultContext .F32) last finished .Body (.Value .F32) hend)]
  exact loop_done f32Bytes env (resultContext .F32) finished hfc hfp

theorem f32_body_validated (env : module.Env) :
    Wasm.Validated f32Bytes env (resultContext .F32) (.Value .F32) :=
  code.validate_body.wasm_sound f32Bytes env (resultContext .F32) (.Value .F32) rfl
    (f32_body_accepted env)

theorem f64_body_accepted (env : module.Env) :
    code.validate_body f64Bytes env (resultContext .F64) = .ok (.Ok ()) := by
  let initial := Body.initial (.Value .F64)
  let first := { initial with pos := 1#usize }
  have hencoded : FloatBits.Decoded 8 f64Bytes 1#usize (0xFFF8000000000001#u64).val 9#usize := by
    refine ⟨[1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0xF8#u8, 0xFF#u8], rfl, rfl, by decide, rfl, ?_⟩
    norm_num [FloatBits.payload]
  have hleb := reader.read_f64_bits.complete f64Bytes 1#usize 0xFFF8000000000001#u64 9#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_f64_const.from_read first f64Bytes 0xFFF8000000000001#u64 9#usize hleb
      (by simp [first, initial, Body.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 10#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .F64, Control.signature (.Value .F64), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Body.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .F64)).map code.StackType.Val := by
    simpa [last, first, initial, Body.initial, Control.results] using hv
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
    (by simp [initial, Body.initial])
    (read_at f64Bytes initial 1#usize code.OP_F64_CONST (by decide) rfl
      (by simp [f64Bytes, bytes, initial, Body.initial, code.OP_F64_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step f64Bytes env (resultContext .F64) pushed last finished code.OP_END
    (by simp [hc, first, initial, Body.initial])
    (read_at f64Bytes pushed 10#usize code.OP_END (by simp [hp, f64Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f64Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f64Bytes env (resultContext .F64) last finished .Body (.Value .F64) hend)]
  exact loop_done f64Bytes env (resultContext .F64) finished hfc hfp

theorem f64_body_validated (env : module.Env) :
    Wasm.Validated f64Bytes env (resultContext .F64) (.Value .F64) :=
  code.validate_body.wasm_sound f64Bytes env (resultContext .F64) (.Value .F64) rfl
    (f64_body_accepted env)

/-- Translation retains IEEE negative zero, rather than identifying it with positive zero. -/
theorem f32_negative_zero : ScalarConst.floatValue 23 8 (0x80000000#u32).val = .NEG (.SUBNORM 0) := by
  decide

/-- Both the sign and the nonzero NaN payload survive translation. -/
theorem f64_nan_payload : ScalarConst.floatValue 52 11 (0xFFF8000000000001#u64).val =
    .NEG (.NAN 0x8000000000001) := by
  decide

def truncatedF64Bytes : Slice U8 := bytes [0x44#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]
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

/-- Truncation is rejected by the actual public body API. -/
theorem truncated_f64_body_rejected (env : module.Env) :
    code.validate_body truncatedF64Bytes env (resultContext .F64) = .ok (.Err .UnexpectedEof) := by
  let first := { Body.initial (.Value .F64) with pos := 1#usize }
  have hread := code.read_f64_const.failed_read first truncatedF64Bytes .UnexpectedEof truncated_f64_reader
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first truncatedF64Bytes env
      (resultContext .F64) code.OP_F64_CONST () = .ok (.Err .UnexpectedEof, first, ()) := by
    simp [global_simps, hread, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop truncatedF64Bytes env (resultContext .F64) (.Value .F64) (.Err .UnexpectedEof)
    (by simp [truncatedF64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error truncatedF64Bytes env (resultContext .F64) (Body.initial (.Value .F64)) first first
    code.OP_F64_CONST .UnexpectedEof (by simp [Body.initial])
    (read_at truncatedF64Bytes (Body.initial (.Value .F64)) 1#usize code.OP_F64_CONST (by decide) rfl
      (by simp [truncatedF64Bytes, bytes, Body.initial, code.OP_F64_CONST, alloc.vec.Vec.deref])) hstep

/-- An unterminated ten-byte signed LEB is rejected before any missing final end matters. -/
theorem overlong_i64_body_rejected (env : module.Env) :
    code.validate_body overlongI64Bytes env (resultContext .I64) = .ok (.Err .LebTooLong) := by
  let first := { Body.initial (.Value .I64) with pos := 1#usize }
  have hread := code.read_i64_const.failed_read first overlongI64Bytes .LebTooLong overlong_i64_reader
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first overlongI64Bytes env
      (resultContext .I64) code.OP_I64_CONST () = .ok (.Err .LebTooLong, first, ()) := by
    simp [global_simps, hread, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop overlongI64Bytes env (resultContext .I64) (.Value .I64) (.Err .LebTooLong)
    (by simp [overlongI64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error overlongI64Bytes env (resultContext .I64) (Body.initial (.Value .I64)) first first
    code.OP_I64_CONST .LebTooLong (by simp [Body.initial])
    (read_at overlongI64Bytes (Body.initial (.Value .I64)) 1#usize code.OP_I64_CONST (by decide) rfl
      (by simp [overlongI64Bytes, bytes, Body.initial, code.OP_I64_CONST, alloc.vec.Vec.deref])) hstep

end Itasca.WasmScalarExamples
