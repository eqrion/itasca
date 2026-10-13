import Itasca.Wasm1.Loop
import Itasca.Handler.End
import Itasca.Handler.SimplePrefix
import Itasca.Handler.SignedConst
import Itasca.Examples.Wasm1.Support

open Aeneas Aeneas.Std

namespace Itasca.Examples.Wasm1Body

open Wasm1Support

def emptyContext : code.Context := ⟨alloc.vec.Vec.new _, alloc.vec.Vec.new _⟩

def endBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [11#u8] (by scalar_tac))

def nopBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [1#u8, 11#u8] (by scalar_tac))

def trailingBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [11#u8, 1#u8] (by scalar_tac))

private theorem step_nop (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (st : code.OpIterState) :
    code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor st data env ctx code.OP_NOP () =
      .ok (.Ok (), st, ()) := by
  simp [global_simps, code.OpVisitor.on_nop.default, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- The public extracted validator really accepts the empty instruction sequence plus its end. -/
theorem empty_body_accepted (env : module.Env) :
    code.validate_body endBytes env emptyContext = .ok (.Ok ()) := by
  let st := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty st [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop endBytes env emptyContext .Empty (.Ok ())
    (by simp [endBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step endBytes env emptyContext (Wasm1.Loop.initial .Empty) st finished code.OP_END
    (by simp [Wasm1.Loop.initial])
    (read_at endBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_END (by decide) rfl (by simp [endBytes, Wasm1.Loop.initial, code.OP_END, alloc.vec.Vec.deref]))
    (step_end endBytes env emptyContext st finished .Body .Empty hend)]
  apply loop_done endBytes env emptyContext finished hc
  exact hp

/-- A nonempty instruction sequence reaches the same public acceptance path. -/
theorem nop_body_accepted (env : module.Env) :
    code.validate_body nopBytes env emptyContext = .ok (.Ok ()) := by
  let first := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  let last := { Wasm1.Loop.initial .Empty with pos := 2#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty last [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop nopBytes env emptyContext .Empty (.Ok ())
    (by simp [nopBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step nopBytes env emptyContext (Wasm1.Loop.initial .Empty) first first code.OP_NOP
    (by simp [Wasm1.Loop.initial])
    (read_at nopBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_NOP (by decide) rfl
      (by simp [nopBytes, Wasm1.Loop.initial, code.OP_NOP, alloc.vec.Vec.deref]))
    (step_nop nopBytes env emptyContext first)]
  rw [loop_step nopBytes env emptyContext first last finished code.OP_END
    (by simp [first, Wasm1.Loop.initial])
    (read_at nopBytes first 2#usize code.OP_END (by decide) rfl
      (by simp [nopBytes, first, code.OP_END, alloc.vec.Vec.deref]))
    (step_end nopBytes env emptyContext last finished .Body .Empty hend)]
  exact loop_done nopBytes env emptyContext finished hc hp

/-- Bytes after the function's closing end are rejected by the public driver. -/
theorem trailing_body_rejected (env : module.Env) :
    code.validate_body trailingBytes env emptyContext = .ok (.Err .TrailingBytes) := by
  let st := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty st [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  apply public_of_loop trailingBytes env emptyContext .Empty (.Err .TrailingBytes)
    (by simp [trailingBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step trailingBytes env emptyContext (Wasm1.Loop.initial .Empty) st finished code.OP_END
    (by simp [Wasm1.Loop.initial])
    (read_at trailingBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_END (by decide) rfl
      (by simp [trailingBytes, Wasm1.Loop.initial, code.OP_END, alloc.vec.Vec.deref]))
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
  let initial := Wasm1.Loop.initial (.Value .I32)
  let first := { initial with pos := 1#usize }
  have hencoded : SignedLeb32.Decoded constBytes 1#usize (42#i32).val 2#usize := by
    refine ⟨[42#u8], rfl, rfl, by decide, [], 42#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  have hleb := reader.read_s32_leb.complete constBytes 1#usize 42#i32 2#usize hencoded
  obtain ⟨⟨_, pushed⟩, hconst, rfl, hv, hc, hp⟩ := WP.spec_imp_exists
    (code.read_i32_const.from_read first constBytes 42#i32 2#usize hleb
      (by simp [first, initial, Wasm1.Loop.initial]; scalar_tac))
  dsimp only at hv hc hp
  let last := { pushed with pos := 3#usize }
  have hctrls : last.ctrls.val = [⟨.Body, .Value .I32, Control.signature (.Value .I32), 0#usize, false⟩] := by
    simp [last, hc, first, initial, Wasm1.Loop.initial]
  have hvals : last.vals.val = [] ++
      (Control.results (code.BlockType.Value .I32)).map code.StackType.Val := by
    simpa [last, first, initial, Wasm1.Loop.initial, Control.results] using hv
  obtain ⟨⟨_, finished⟩, hend, rfl, hfc, hfv, hfp⟩ := WP.spec_imp_exists
    (code.read_end.concrete last [] ⟨.Body, .Value .I32, Control.signature (.Value .I32), 0#usize, false⟩ [] hctrls hvals rfl
      (by simp))
  dsimp only at hfc hfv hfp
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first constBytes env
      i32Context code.OP_I32_CONST () = .ok (.Ok (), pushed, ()) := by
    simp [global_simps, hconst, code.OpVisitor.on_i32_const.default, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch]
  apply public_of_loop constBytes env i32Context (.Value .I32) (.Ok ())
    (by simp [constBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step constBytes env i32Context initial first pushed code.OP_I32_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at constBytes initial 1#usize code.OP_I32_CONST (by decide) rfl
      (by simp [constBytes, initial, Wasm1.Loop.initial, code.OP_I32_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step constBytes env i32Context pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at constBytes pushed 3#usize code.OP_END (by simp [hp, constBytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, constBytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end constBytes env i32Context last finished .Body (.Value .I32) hend)]
  exact loop_done constBytes env i32Context finished hfc hfp

def dropBytes : Slice U8 :=
  alloc.vec.Vec.deref (alloc.vec.Vec.from [26#u8, 11#u8] (by scalar_tac))

/-- A lexically valid core body can still reject: reachable DROP has no operand. -/
theorem drop_body_rejected (env : module.Env) :
    code.validate_body dropBytes env emptyContext = .ok (.Err .EmptyStack) := by
  let first := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  have hpop := code.pop_stack_type.at_base first rfl
  have hpop' : code.pop_stack_type first = .ok (.Err .EmptyStack, first) := by
    simpa [first, Control.polymorphic, Wasm1.Loop.initial] using hpop
  have hstep : code.step code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor first dropBytes env
      emptyContext code.OP_DROP () = .ok (.Err .EmptyStack, first, ()) := by
    simp [global_simps, code.read_drop, hpop',
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  apply public_of_loop dropBytes env emptyContext .Empty (.Err .EmptyStack)
    (by simp [dropBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  exact loop_error dropBytes env emptyContext (Wasm1.Loop.initial .Empty) first first code.OP_DROP
    .EmptyStack (by simp [Wasm1.Loop.initial])
    (read_at dropBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_DROP (by decide) rfl
      (by simp [dropBytes, Wasm1.Loop.initial, code.OP_DROP, alloc.vec.Vec.deref])) hstep

end Itasca.Examples.Wasm1Body
