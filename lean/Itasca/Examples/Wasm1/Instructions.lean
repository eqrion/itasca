import Itasca.Wasm1.Soundness
import Itasca.Handler.EnvDispatch
import Itasca.Examples.Wasm1.Support

/-!
# Wasm 1.0 instruction examples

Short bodies for single instructions run through `code.validate_body`: `local.get`, `memory.size`
with its reserved byte, `select` and `drop` after `unreachable`, a direct `call`, `global.set` on
an immutable global, an unknown opcode and trailing bytes. Each shows an environment lookup, an
immediate check or the polymorphic stack rule that the extracted code performs, with the exact
accepted result or error.
-/

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1Instructions

open Wasm1Support


/-- A context with no locals and no results. -/
def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- A context with no locals and one `i32` result. -/
def i32Context : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

/-- A context with one `i32` local and one `i32` result. -/
def localContext : code.Context :=
  ⟨alloc.vec.Vec.from [.I32] (by scalar_tac), alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

private theorem single_accepted (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (opcode : U8) (s : code.OpIterState)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val) (hresults : ctx.results.val = Control.results bt)
    (hfirst : 0 < data.length) (hbyte : data.val[0] = opcode)
    (hend : s.pos.val < data.length) (hendbyte : data.val[s.pos.val] = code.OP_END)
    (hendpos : (Slice.len data).val = s.pos.val + 1)
    (hctrls : s.ctrls = (Wasm1.Loop.initial bt).ctrls)
    (hvals : s.vals.val = (Control.results bt).map code.StackType.Val)
    (hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      {Wasm1.Loop.initial bt with pos := 1#usize} data env ctx opcode () = .ok (.Ok (), s, ())) :
    code.validate_body data env ctx = .ok (.Ok ()) := by
  let last := {s with pos := Slice.len data}
  obtain ⟨⟨_, finished⟩, hr, rfl, hc, _, hp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, bt, Control.signature (bt), 0#usize, false⟩ []
      (by simp [last, hctrls, Wasm1.Loop.initial]) (by simpa [last] using hvals) rfl (by simp))
  dsimp only at hc hp
  apply public_of_loop data env ctx bt (.Ok ()) hsize hresults
  rw [loop_step data env ctx (Wasm1.Loop.initial bt) {Wasm1.Loop.initial bt with pos := 1#usize} s opcode
    (by simp [Wasm1.Loop.initial]) (read_at data (Wasm1.Loop.initial bt) 1#usize opcode hfirst rfl hbyte) hstep]
  rw [loop_step data env ctx s last finished code.OP_END (by simp [hctrls, Wasm1.Loop.initial])
    (read_at data s (Slice.len data) code.OP_END hend hendpos hendbyte)
    (step_end data env ctx last finished .Body bt hr)]
  exact loop_done data env ctx finished hc hp

private theorem zero_leb (data : Slice U8) (pos next : Usize) (hp : pos.val < data.length)
    (hz : data.val[pos.val] = 0#u8) (hn : next.val = pos.val + 1) :
    reader.read_u32_leb data pos = .ok (.Ok (0#u32, next)) := by
  obtain ⟨idx, p, hr, hi, hnext⟩ := reader.read_u32_leb.single_byte data pos hp (by simp [hz])
  have hzidx : idx = 0#u32 := by apply UScalar.eq_of_val_eq; simpa [hz] using hi
  have hpnext : p = next := UScalar.eq_of_val_eq (hnext.trans hn.symm)
  simpa [hzidx, hpnext] using hr

private theorem zero_byte (data : Slice U8) (st : code.OpIterState) (next : Usize)
    (hp : st.pos.val < data.length) (hz : data.val[st.pos.val] = 0#u8)
    (hn : next.val = st.pos.val + 1) :
    code.read_reserved_zero st data = .ok (.Ok (), {st with pos := next}) := by
  obtain ⟨r, hr, p, rfl, hnext⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
  have hpnext : p = next := UScalar.eq_of_val_eq (hnext.trans hn.symm)
  simp [code.read_reserved_zero, hr, hpnext, hz, core.result.Result.Insts.CoreOpsTry.branch]

/-- `code.validate_body` accepts `local.get 0; end` (`20 00 0b`) in `localContext`: local 0 is
looked up in the context and its `i32` type matches the result. -/
theorem local_get_accepted (env : module.Env) :
    code.validate_body (bytes [0x20#u8, 0#u8, 0x0B#u8]) env localContext = .ok (.Ok ()) := by
  let data := bytes [0x20#u8, 0#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial (.Value .I32) with pos := 1#usize}
  have hlookup : code.local_type localContext 0#u32 = .ok (.Ok .I32) := by
    obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (code.local_type.spec localContext 0#u32)
    cases r with
    | Err e => simp [localContext] at ht
    | Ok t =>
        have hty : t = .I32 := by simpa [localContext] using ht.choose_spec.symm
        simpa [hty] using hr
  have hleb := zero_leb data 1#usize 2#usize (by decide) rfl rfl
  have htake : code.take_local first data localContext =
      .ok (.Ok (0#u32, .I32), {first with pos := 2#usize}) := by
    simp [code.take_local, first, hleb, hlookup, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨s, hpush, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.push_val.spec {first with pos := 2#usize} (.Val .I32) (by simp [first, Wasm1.Loop.initial]; scalar_tac))
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env localContext code.OP_LOCAL_GET () =
      .ok (.Ok (), s, ()) := by
    rw [code.step_local_get.dispatch]
    simp [CoreVisitor.run, code.read_local_get, htake, hpush, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_local_get.default, code.visit]
  apply single_accepted data env localContext (.Value .I32) code.OP_LOCAL_GET s
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl (by decide) (by simp [data, bytes, alloc.vec.Vec.deref, code.OP_LOCAL_GET])
    (by simp [hp, data, bytes, alloc.vec.Vec.deref]) (by simp [hp, data, bytes, alloc.vec.Vec.deref, code.OP_END])
    (by simp [hp, data, bytes, alloc.vec.Vec.deref]) hc _ hstep
  simpa [first, Wasm1.Loop.initial, Control.results] using hv

/-- The accepted `local.get` body has a `Wasm1.Validated` certificate. -/
theorem local_get_validated (env : module.Env) :
    Wasm1.Validated (bytes [0x20#u8, 0#u8, 0x0B#u8]) env localContext (.Value .I32) :=
  code.validate_body.wasm_sound _ env localContext (.Value .I32) rfl (local_get_accepted env)

/-- `code.validate_body` accepts `memory.size; end` (`3f 00 0b`) with an `i32` result when the
environment has a memory, consuming the reserved zero byte. -/
theorem memory_size_accepted (env : module.Env) (hmem : env.mem_types.val ≠ []) :
    code.validate_body (bytes [0x3F#u8, 0#u8, 0x0B#u8]) env i32Context = .ok (.Ok ()) := by
  let data := bytes [0x3F#u8, 0#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial (.Value .I32) with pos := 1#usize}
  have hreserved := zero_byte data first 2#usize (by simp [data, first, bytes, alloc.vec.Vec.deref]) rfl rfl
  have hrequire : code.require_memory env = .ok (.Ok ()) := by
    simp [code.require_memory, alloc.vec.Vec.is_empty, hmem]
  obtain ⟨s, hpush, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.push_val.spec {first with pos := 2#usize} (.Val .I32) (by simp [first, Wasm1.Loop.initial]; scalar_tac))
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env i32Context code.OP_MEMORY_SIZE () =
      .ok (.Ok (), s, ()) := by
    rw [code.step_memory_size.dispatch]
    simp [CoreVisitor.run, code.read_memory_size, hreserved, hrequire, hpush,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_memory_size.default, code.visit]
  apply single_accepted data env i32Context (.Value .I32) code.OP_MEMORY_SIZE s
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl (by simp [data, bytes, alloc.vec.Vec.deref])
    (by simp [data, bytes, alloc.vec.Vec.deref, code.OP_MEMORY_SIZE])
    (by simp [hp, data, bytes, alloc.vec.Vec.deref]) (by simp [hp, data, bytes, alloc.vec.Vec.deref, code.OP_END])
    (by simp [hp, data, bytes, alloc.vec.Vec.deref]) hc _ hstep
  simpa [first, Wasm1.Loop.initial, Control.results] using hv

/-- The accepted `memory.size` body has a `Wasm1.Validated` certificate. -/
theorem memory_size_validated (env : module.Env) (hmem : env.mem_types.val ≠ []) :
    Wasm1.Validated (bytes [0x3F#u8, 0#u8, 0x0B#u8]) env i32Context (.Value .I32) :=
  code.validate_body.wasm_sound _ env i32Context (.Value .I32) rfl (memory_size_accepted env hmem)

/-- `3f 01 0b` is rejected with `ReservedByteNotZero`, before any memory lookup. -/
theorem reserved_byte_rejected (env : module.Env) :
    code.validate_body (bytes [0x3F#u8, 1#u8, 0x0B#u8]) env i32Context =
      .ok (.Err .ReservedByteNotZero) := by
  let data := bytes [0x3F#u8, 1#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial (.Value .I32) with pos := 1#usize}
  obtain ⟨r, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data first.pos (by decide))
  have hb : data.val[first.pos.val]'(by decide) = 1#u8 := rfl
  have hreserved : code.read_reserved_zero first data = .ok (.Err .ReservedByteNotZero, first) := by
    simp [code.read_reserved_zero, hr, hb, core.result.Result.Insts.CoreOpsTry.branch]
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env i32Context code.OP_MEMORY_SIZE () =
      .ok (.Err .ReservedByteNotZero, first, ()) := by
    rw [code.step_memory_size.dispatch]
    simp [CoreVisitor.run, code.read_memory_size, hreserved, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop data env i32Context (.Value .I32) (.Err .ReservedByteNotZero)
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error data env i32Context (Wasm1.Loop.initial (.Value .I32)) first first code.OP_MEMORY_SIZE
    .ReservedByteNotZero (by simp [Wasm1.Loop.initial])
    (read_at data (Wasm1.Loop.initial (.Value .I32)) 1#usize code.OP_MEMORY_SIZE (by decide) rfl
      (by simp [data, bytes, alloc.vec.Vec.deref, code.OP_MEMORY_SIZE, Wasm1.Loop.initial])) hstep

private theorem finish_empty (data : Slice U8) (env : module.Env)
    (st : code.OpIterState) (poly : Bool)
    (hc : st.ctrls.val = [⟨.Body, .Empty, Control.signature (.Empty), 0#usize, poly⟩]) (hv : st.vals.val = [])
    (hp : st.pos.val < data.length) (hb : data.val[st.pos.val] = code.OP_END)
    (hn : (Slice.len data).val = st.pos.val + 1) :
    code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env emptyContext.locals emptyContext.results () st = .ok (.Ok (), ()) := by
  let last := {st with pos := Slice.len data}
  obtain ⟨⟨_, finished⟩, hr, rfl, hfc, _, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, poly⟩ [] hc
      (by simpa [last, Control.results] using hv) rfl (by simp))
  dsimp only at hfc hfp
  rw [loop_step data env emptyContext st last finished code.OP_END (by simp [hc])
    (read_at data st (Slice.len data) code.OP_END hp hn hb)
    (step_end data env emptyContext last finished .Body .Empty hr)]
  exact loop_done data env emptyContext finished hfc hfp

/-- `unreachable; select; drop; end` (`00 1b 1a 0b`) is accepted: `select` takes its operands from
the polymorphic base of the stack, and `drop` consumes its bottom-typed result. -/
theorem polymorphic_select_accepted (env : module.Env) :
    code.validate_body (bytes [0#u8, 0x1B#u8, 0x1A#u8, 0x0B#u8]) env emptyContext = .ok (.Ok ()) := by
  let data := bytes [0#u8, 0x1B#u8, 0x1A#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial .Empty with pos := 1#usize}
  obtain ⟨s1, hm, hv1, _, hc1, hp1⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec first [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl (by simp [first, Wasm1.Loop.initial]))
  have hv1' : s1.vals.val = [] := by simpa [first, Wasm1.Loop.initial] using hv1
  have hunreachable : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env emptyContext
      code.OP_UNREACHABLE () = .ok (.Ok (), s1, ()) := by
    simp [global_simps, code.read_unreachable, hm, code.OpVisitor.on_unreachable.default,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  let second := {s1 with pos := 2#usize}
  have hbase : alloc.vec.Vec.len second.vals = Control.base second := by
    apply UScalar.eq_of_val_eq
    simp [second, hv1', Control.base, hc1]
  have hpoly : Control.polymorphic second = true := by simp [second, Control.polymorphic, hc1]
  have hcond := code.pop_with_type.polymorphic second .I32 hbase hpoly
  have hpop : code.pop_stack_type second = .ok (.Ok .Bot, second) := by
    simpa [hpoly] using code.pop_stack_type.at_base second hbase
  obtain ⟨s2, hpush, hv2, hc2, hp2⟩ := WP.spec_imp_exists
    (code.push_val.spec second .Bot (by simp [second, hv1']; scalar_tac))
  have hv2' : s2.vals.val = [.Bot] := by simpa [second, hv1'] using hv2
  have hselect : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor second data env emptyContext
      code.OP_SELECT () = .ok (.Ok (), s2, ()) := by
    rw [code.step_select.dispatch]
    simp [CoreVisitor.run, code.read_select, hcond, hpop, code.join_stack_type, hpush, code.is_select_type,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_select.default, code.visit]
  let third := {s2 with pos := 3#usize}
  obtain ⟨⟨_, s3⟩, hd, rfl, hv3, hc3, hp3⟩ := WP.spec_imp_exists
    (code.pop_stack_type.above_base third [] .Bot (by simpa [third] using hv2')
      (by simp [third, Control.base, hc2, second, hc1]))
  dsimp only at hv3 hc3 hp3
  have hdrop : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor third data env emptyContext
      code.OP_DROP () = .ok (.Ok (), s3, ()) := by
    simp [global_simps, code.read_drop, hd, code.OpVisitor.on_drop.default,
      code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop data env emptyContext .Empty (.Ok ())
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step data env emptyContext (Wasm1.Loop.initial .Empty) first s1 code.OP_UNREACHABLE
    (by simp [Wasm1.Loop.initial])
    (read_at data (Wasm1.Loop.initial .Empty) 1#usize code.OP_UNREACHABLE (by decide) rfl
      (by simp [data, bytes, alloc.vec.Vec.deref, Wasm1.Loop.initial, code.OP_UNREACHABLE])) hunreachable]
  rw [loop_step data env emptyContext s1 second s2 code.OP_SELECT (by simp [hc1])
    (read_at data s1 2#usize code.OP_SELECT (by simp [hp1, first, data, bytes, alloc.vec.Vec.deref])
      (by simp [hp1, first]) (by simp [hp1, first, data, bytes, alloc.vec.Vec.deref, code.OP_SELECT])) hselect]
  rw [loop_step data env emptyContext s2 third s3 code.OP_DROP (by simp [hc2, second, hc1])
    (read_at data s2 3#usize code.OP_DROP (by simp [hp2, second, data, bytes, alloc.vec.Vec.deref])
      (by simp [hp2, second]) (by simp [hp2, second, data, bytes, alloc.vec.Vec.deref, code.OP_DROP])) hdrop]
  exact finish_empty data env s3 true (by simp [hc3, third, hc2, second, hc1]) hv3
    (by simp [hp3, third, data, bytes, alloc.vec.Vec.deref])
    (by simp [hp3, third, data, bytes, alloc.vec.Vec.deref, code.OP_END])
    (by simp [hp3, third, data, bytes, alloc.vec.Vec.deref])

/-- The accepted `select` body has a `Wasm1.Validated` certificate. -/
theorem polymorphic_select_validated (env : module.Env) :
    Wasm1.Validated (bytes [0#u8, 0x1B#u8, 0x1A#u8, 0x0B#u8]) env emptyContext .Empty :=
  code.validate_body.wasm_sound _ env emptyContext .Empty rfl (polymorphic_select_accepted env)

/-- The body `ff` is rejected with `UnrecognizedOpcode`. -/
theorem unknown_opcode_rejected (env : module.Env) :
    code.validate_body (bytes [0xFF#u8]) env emptyContext = .ok (.Err .UnrecognizedOpcode) := by
  let data := bytes [0xFF#u8]
  let first := {Wasm1.Loop.initial .Empty with pos := 1#usize}
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env emptyContext 0xFF#u8 () =
      .ok (.Err .UnrecognizedOpcode, first, ()) := by
    simp [code.step_numeric, global_simps]
  apply public_of_loop data env emptyContext .Empty (.Err .UnrecognizedOpcode)
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error data env emptyContext (Wasm1.Loop.initial .Empty) first first 0xFF#u8
    .UnrecognizedOpcode (by simp [Wasm1.Loop.initial])
    (read_at data (Wasm1.Loop.initial .Empty) 1#usize 0xFF#u8 (by decide) rfl rfl) hstep

/-- The function type `[] -> []`. -/
def voidFunction : types.FuncType := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

/-- `call 0; end` (`10 00 0b`) is accepted when the resolved function cache `func_types` holds
`[] -> []`. The theorem assumes nothing about the module's type-index list. -/
theorem cached_call_accepted (env : module.Env) (hfun : env.func_types.val = [voidFunction]) :
    code.validate_body (bytes [0x10#u8, 0#u8, 0x0B#u8]) env emptyContext = .ok (.Ok ()) := by
  let data := bytes [0x10#u8, 0#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial .Empty with pos := 1#usize}
  let decoded := {first with pos := 2#usize}
  have hleb := zero_leb data 1#usize 2#usize (by simp [data, bytes, alloc.vec.Vec.deref]) rfl rfl
  have htake : code.take_index first data = .ok (.Ok (0#u32), decoded) := by
    simp [code.take_index, first, decoded, hleb, core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨ft, hft, heq⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec env.func_types (UScalar.cast .Usize 0#u32) (by simp [hfun]))
  have htype : ft = voidFunction := by simpa [hfun] using heq
  subst ft
  have hrequire : code.require_single_result (alloc.vec.Vec.deref voidFunction.results) = .ok (.Ok ()) := by
    simp [code.require_single_result, voidFunction, alloc.vec.Vec.deref, limits.MAX_RESULTS]
  have hpop := code.pop_types.empty decoded (alloc.vec.Vec.deref voidFunction.params) rfl
  obtain ⟨s, hpush, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.push_types.spec decoded (alloc.vec.Vec.deref voidFunction.results)
      (by simp [decoded, first, Wasm1.Loop.initial, voidFunction, alloc.vec.Vec.deref]))
  have hcall : code.read_call first data env = .ok (.Ok (0#u32), s) := by
    simp [code.read_call, htake, lift, hfun, hft, hrequire, hpop, hpush,
      core.result.Result.Insts.CoreOpsTry.branch]
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env emptyContext code.OP_CALL () =
      .ok (.Ok (), s, ()) := by
    rw [code.step_call.dispatch]
    simp [CoreVisitor.run, hcall, core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_call.default, code.visit]
  apply single_accepted data env emptyContext .Empty code.OP_CALL s
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
    (by simp [data, bytes, alloc.vec.Vec.deref]) (by simp [data, bytes, alloc.vec.Vec.deref, code.OP_CALL])
    (by simp [hp, decoded, data, bytes, alloc.vec.Vec.deref])
    (by simp [hp, decoded, data, bytes, alloc.vec.Vec.deref, code.OP_END])
    (by simp [hp, decoded, data, bytes, alloc.vec.Vec.deref]) hc _ hstep
  simpa [decoded, first, Wasm1.Loop.initial, Control.results, voidFunction, alloc.vec.Vec.deref] using hv

/-- The accepted `call` body has a `Wasm1.Validated` certificate. -/
theorem cached_call_validated (env : module.Env) (hfun : env.func_types.val = [voidFunction]) :
    Wasm1.Validated (bytes [0x10#u8, 0#u8, 0x0B#u8]) env emptyContext .Empty :=
  code.validate_body.wasm_sound _ env emptyContext .Empty rfl (cached_call_accepted env hfun)

/-- `global.set 0; end` (`24 00 0b`) on an immutable `i32` global is rejected with
`ImmutableGlobal`, before any operand is popped. -/
theorem immutable_global_rejected (env : module.Env)
    (hglobal : env.global_types.val = [⟨.Const, .I32⟩]) :
    code.validate_body (bytes [0x24#u8, 0#u8, 0x0B#u8]) env emptyContext = .ok (.Err .ImmutableGlobal) := by
  let data := bytes [0x24#u8, 0#u8, 0x0B#u8]
  let first := {Wasm1.Loop.initial .Empty with pos := 1#usize}
  let decoded := {first with pos := 2#usize}
  have hlookup : code.global_type env 0#u32 = .ok (.Ok ⟨.Const, .I32⟩) := by
    obtain ⟨r, hr, ht⟩ := WP.spec_imp_exists (code.global_type.spec env 0#u32)
    cases r with
    | Err e => simp [hglobal] at ht
    | Ok gt =>
        have hgt : gt = ⟨.Const, .I32⟩ := by simpa [hglobal] using ht.choose_spec.symm
        simpa [hgt] using hr
  have hleb := zero_leb data 1#usize 2#usize (by simp [data, bytes, alloc.vec.Vec.deref]) rfl rfl
  have htake : code.take_global first data env = .ok (.Ok (0#u32, ⟨.Const, .I32⟩), decoded) := by
    simp [code.take_global, first, decoded, hleb, hlookup, core.result.Result.Insts.CoreOpsTry.branch]
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first data env emptyContext code.OP_GLOBAL_SET () =
      .ok (.Err .ImmutableGlobal, decoded, ()) := by
    rw [code.step_global_set.dispatch]
    simp [CoreVisitor.run, code.read_global_set, htake, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop data env emptyContext .Empty (.Err .ImmutableGlobal)
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error data env emptyContext (Wasm1.Loop.initial .Empty) first decoded code.OP_GLOBAL_SET
    .ImmutableGlobal (by simp [Wasm1.Loop.initial])
    (read_at data (Wasm1.Loop.initial .Empty) 1#usize code.OP_GLOBAL_SET (by simp [data, bytes, alloc.vec.Vec.deref, Wasm1.Loop.initial]) rfl
      (by simp [data, bytes, alloc.vec.Vec.deref, Wasm1.Loop.initial, code.OP_GLOBAL_SET])) hstep

/-- The body `0b 01` is rejected with `TrailingBytes`. -/
theorem trailing_bytes_rejected (env : module.Env) :
    code.validate_body (bytes [0x0B#u8, 1#u8]) env emptyContext = .ok (.Err .TrailingBytes) := by
  let data := bytes [0x0B#u8, 1#u8]
  let first := {Wasm1.Loop.initial .Empty with pos := 1#usize}
  obtain ⟨⟨_, finished⟩, hr, rfl, hc, _, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty first [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hp
  apply public_of_loop data env emptyContext .Empty (.Err .TrailingBytes)
    (by simp [data, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step data env emptyContext (Wasm1.Loop.initial .Empty) first finished code.OP_END
    (by simp [Wasm1.Loop.initial])
    (read_at data (Wasm1.Loop.initial .Empty) 1#usize code.OP_END (by decide) rfl
      (by simp [data, bytes, alloc.vec.Vec.deref, Wasm1.Loop.initial, code.OP_END]))
    (step_end data env emptyContext first finished .Body .Empty hr)]
  apply loop_trailing data env emptyContext finished hc
  intro heq
  have hn := congrArg UScalar.val heq
  simp [hp, first, data, bytes, alloc.vec.Vec.deref] at hn

end Itasca.Examples.Wasm1Instructions
