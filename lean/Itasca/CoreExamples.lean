import Itasca.CoreSoundness
import Itasca.Nop
import Itasca.Body
import Itasca.End
import Itasca.CoreSimple
import Itasca.SignedConst

open Aeneas Aeneas.Std

namespace Itasca.CoreExamples

def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

def endBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [11#u8] (by scalar_tac))

def nopBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [1#u8, 11#u8] (by scalar_tac))

def trailingBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [11#u8, 1#u8] (by scalar_tac))

private theorem public_of_loop (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (bt : code.BlockType) (result : core.result.Result Unit error.OpError)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hresults : ctx.results.val = Control.results bt)
    (hloop : code.validate_body_with_loop code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor
      data env ctx.locals ctx.results () (Body.initial bt) = .ok (result, ())) :
    code.validate_body data env ctx = .ok result := by
  have hguard : ¬ Slice.len data > limits.MAX_FUNCTION_BYTES := by scalar_tac
  simp [code.validate_body, code.validate_body_with, hguard,
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

/-- The public extracted validator really accepts the empty instruction sequence plus its end. -/
theorem empty_body_accepted (env : module.Env) :
    code.validate_body endBytes env emptyContext = .ok (.Ok ()) := by
  let st := { Body.initial .Empty with pos := 1#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty st [] ⟨.Body, .Empty, 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop endBytes env emptyContext .Empty (.Ok ())
    (by simp [endBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step endBytes env emptyContext (Body.initial .Empty) st finished code.OP_END
    (by simp [Body.initial])
    (read_at endBytes (Body.initial .Empty) 1#usize code.OP_END (by decide) rfl (by simp [endBytes, Body.initial, code.OP_END, alloc.vec.Vec.deref]))
    (step_end endBytes env emptyContext st finished .Body .Empty hend)]
  apply loop_done endBytes env emptyContext finished hc
  exact hp

/-- A nonempty instruction sequence reaches the same public acceptance path. -/
theorem nop_body_accepted (env : module.Env) :
    code.validate_body nopBytes env emptyContext = .ok (.Ok ()) := by
  let first := { Body.initial .Empty with pos := 1#usize }
  let last := { Body.initial .Empty with pos := 2#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty last [] ⟨.Body, .Empty, 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop nopBytes env emptyContext .Empty (.Ok ())
    (by simp [nopBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step nopBytes env emptyContext (Body.initial .Empty) first first code.OP_NOP
    (by simp [Body.initial])
    (read_at nopBytes (Body.initial .Empty) 1#usize code.OP_NOP (by decide) rfl
      (by simp [nopBytes, Body.initial, code.OP_NOP, alloc.vec.Vec.deref]))
    (code.step_nop _ first nopBytes env emptyContext () () rfl)]
  rw [loop_step nopBytes env emptyContext first last finished code.OP_END
    (by simp [first, Body.initial])
    (read_at nopBytes first 2#usize code.OP_END (by decide) rfl
      (by simp [nopBytes, first, code.OP_END, alloc.vec.Vec.deref]))
    (step_end nopBytes env emptyContext last finished .Body .Empty hend)]
  exact loop_done nopBytes env emptyContext finished hc hp

/-- Bytes after the function's closing end are rejected by the public driver. -/
theorem trailing_body_rejected (env : module.Env) :
    code.validate_body trailingBytes env emptyContext = .ok (.Err .TrailingBytes) := by
  let st := { Body.initial .Empty with pos := 1#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty st [] ⟨.Body, .Empty, 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop trailingBytes env emptyContext .Empty (.Err .TrailingBytes)
    (by simp [trailingBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step trailingBytes env emptyContext (Body.initial .Empty) st finished code.OP_END
    (by simp [Body.initial])
    (read_at trailingBytes (Body.initial .Empty) 1#usize code.OP_END (by decide) rfl
      (by simp [trailingBytes, Body.initial, code.OP_END, alloc.vec.Vec.deref]))
    (step_end trailingBytes env emptyContext st finished .Body .Empty hend)]
  apply loop_trailing trailingBytes env emptyContext finished hc
  simp [hp, st, trailingBytes, alloc.vec.Vec.deref]

def i32Context : code.Context :=
  ⟨alloc.vec.Vec.new _, alloc.vec.Vec.from [.I32] (by scalar_tac)⟩

def constBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [65#u8, 42#u8, 11#u8] (by scalar_tac))

/-- This example exercises signed immediate decoding, result checking, and the public driver. -/
theorem i32_const_body_accepted (env : module.Env) :
    code.validate_body constBytes env i32Context = .ok (.Ok ()) := by
  let initial := Body.initial (.Value .I32)
  let first := { initial with pos := 1#usize }
  have hencoded : SignedLeb.Decoded constBytes 1#usize (42#i32).val 2#usize := by
    refine ⟨[42#u8], rfl, rfl, by decide, [], 42#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  have hleb := reader.read_s32_leb.complete constBytes 1#usize 42#i32 2#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_i32_const.from_read first constBytes 42#i32 2#usize hleb
      (by simp [first, initial, Body.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 3#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .I32, 0#usize, false⟩] := by
    simp [last, hc, first, initial, Body.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .I32)).map code.StackType.Val := by
    simpa [last, first, initial, Body.initial, Control.results] using hv
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Value .I32, 0#usize, false⟩ [] hctrls hvals rfl
      (by simp))
  dsimp only at hfc hfv hfp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first constBytes env
      i32Context code.OP_I32_CONST () = .ok (.Ok (), pushed, ()) := by
    simp [global_simps, hconst, code.OpVisitor.on_i32_const.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop constBytes env i32Context (.Value .I32) (.Ok ())
    (by simp [constBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step constBytes env i32Context initial first pushed code.OP_I32_CONST
    (by simp [initial, Body.initial])
    (read_at constBytes initial 1#usize code.OP_I32_CONST (by decide) rfl
      (by simp [constBytes, initial, Body.initial, code.OP_I32_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step constBytes env i32Context pushed last finished code.OP_END
    (by simp [hc, first, initial, Body.initial])
    (read_at constBytes pushed 3#usize code.OP_END (by simp [hp, constBytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, constBytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end constBytes env i32Context last finished .Body (.Value .I32) hend)]
  exact loop_done constBytes env i32Context finished hfc hfp

def dropBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [26#u8, 11#u8] (by scalar_tac))

/-- A lexically valid core body can still reject: reachable DROP has no operand. -/
theorem drop_body_rejected (env : module.Env) :
    code.validate_body dropBytes env emptyContext = .ok (.Err .EmptyStack) := by
  let first := { Body.initial .Empty with pos := 1#usize }
  have hpop := code.pop_stack_type.at_base first rfl
  have hpop' : code.pop_stack_type first = .ok (.Err .EmptyStack, first) := by
    simpa [first, Control.polymorphic, Body.initial] using hpop
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first dropBytes env
      emptyContext code.OP_DROP () = .ok (.Err .EmptyStack, first, ()) := by
    simp [global_simps, code.read_drop, hpop',
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop dropBytes env emptyContext .Empty (.Err .EmptyStack)
    (by simp [dropBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error dropBytes env emptyContext (Body.initial .Empty) first first code.OP_DROP
    .EmptyStack (by simp [Body.initial])
    (read_at dropBytes (Body.initial .Empty) 1#usize code.OP_DROP (by decide) rfl
      (by simp [dropBytes, Body.initial, code.OP_DROP, alloc.vec.Vec.deref])) hstep

/-- The accepted constant example satisfies the public theorem's independent byte-profile premise. -/
theorem i32_const_profile : Core.Profile constBytes := by
  have hencoding : SignedLeb.Encoding [42#u8] (42#i32).val := by
    refine ⟨[], 42#u8, rfl, by decide, by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  refine ⟨[.i32Const 42#i32, .end_],
    .cons (next := 2#usize) ?_ (.cons (next := 3#usize) ?_ (.nil _ rfl))⟩
  · refine ⟨[42#u8], .i32Const _ hencoding, ?_, rfl, by decide⟩
    simp [Core.Token.opcode, code.OP_I32_CONST, constBytes, alloc.vec.Vec.deref]
  · refine ⟨[], .end_, ?_, rfl, by decide⟩
    simp [Core.Token.opcode, code.OP_END, constBytes, alloc.vec.Vec.deref]

/-- A nonvacuous application of the complete public soundness theorem to real accepted bytes. -/
theorem i32_const_body_validated (env : module.Env) :
    Core.Validated constBytes i32Context (.Value .I32) :=
  code.validate_body.core_sound constBytes env i32Context (.Value .I32) rfl
    i32_const_profile (i32_const_body_accepted env)

end Itasca.CoreExamples
