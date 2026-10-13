import Itasca.Wasm1.Visitor.Refinement
import Itasca.Wasm1.Visitor.Lift
import Itasca.Visitor.EventDispatch
import Itasca.Handler.ControlComplete
import Itasca.Examples.Wasm1.Scalars
import Itasca.Examples.Wasm1.Body
import Itasca.Examples.Wasm1.Support

open Aeneas Aeneas.Std

attribute [local simp] Itasca.Control.signature Itasca.Control.resultView

namespace Itasca.Examples.Wasm1VisitorTrace

open Wasm1Support (public_of_loop_with loop_done_with loop_trailing_with loop_step_with
  loop_error_with read_at bytes)

open VisitorTrace

private def observation (st : code.OpIterState) (action : Action) : Observation :=
  ⟨.op st action, .Ok ()⟩

private theorem step_end (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (log : List Observation) (st next : code.OpIterState) (kind : code.LabelKind) (bt : code.BlockType)
    (hr : code.read_end st = .ok (.Ok (kind, bt), next)) :
    code.step recorder st data env ctx code.OP_END log =
      .ok (.Ok (), next, log ++ [observation next (.end_ kind (Control.signature bt))]) := by
  simp [hr, recorder, ofHandler, observation,
    code.visit, core.result.Result.Insts.CoreOpsTry.branch]

open Examples.Wasm1Scalars in
/-- The callback retains f32's negative-zero sign bit through the actual public body. -/
theorem f32_signed_zero_trace (env : module.Env) :
    ∃ pushed finished, code.validate_body_with recorder f32Bytes env (resultContext .F32) [] =
      .ok (.Ok (), [observation pushed (.f32_const 0x80000000#u32),
        observation finished (.end_ .Body (.Value .F32))]) := by
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
  have hstep : code.step recorder first f32Bytes env (resultContext .F32) code.OP_F32_CONST [] =
      .ok (.Ok (), pushed, [observation pushed (.f32_const 0x80000000#u32)]) := by
    simp [hconst, recorder, ofHandler,
      observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  refine ⟨pushed, finished, ?_⟩
  apply public_of_loop_with recorder f32Bytes env (resultContext .F32) (.Value .F32) (.Ok ()) [] _
    (by simp [f32Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step_with recorder f32Bytes env (resultContext .F32) [] _ initial first pushed code.OP_F32_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at f32Bytes initial 1#usize code.OP_F32_CONST (by decide) rfl
      (by simp [f32Bytes, bytes, initial, Wasm1.Loop.initial, code.OP_F32_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step_with recorder f32Bytes env (resultContext .F32) _ _ pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at f32Bytes pushed 6#usize code.OP_END (by simp [hp, f32Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f32Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f32Bytes env (resultContext .F32) _ last finished .Body (.Value .F32) hend)]
  exact loop_done_with recorder f32Bytes env (resultContext .F32) _ finished hfc hfp

open Examples.Wasm1Scalars in
/-- All 64 raw bits, including NaN sign and payload, reach the f64 callback unchanged. -/
theorem f64_nan_payload_trace (env : module.Env) :
    ∃ pushed finished, code.validate_body_with recorder f64Bytes env (resultContext .F64) [] =
      .ok (.Ok (), [observation pushed (.f64_const 0xFFF8000000000001#u64),
        observation finished (.end_ .Body (.Value .F64))]) := by
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
  have hstep : code.step recorder first f64Bytes env (resultContext .F64) code.OP_F64_CONST [] =
      .ok (.Ok (), pushed, [observation pushed (.f64_const 0xFFF8000000000001#u64)]) := by
    simp [hconst, recorder, ofHandler,
      observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch]
  refine ⟨pushed, finished, ?_⟩
  apply public_of_loop_with recorder f64Bytes env (resultContext .F64) (.Value .F64) (.Ok ()) [] _
    (by simp [f64Bytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step_with recorder f64Bytes env (resultContext .F64) [] _ initial first pushed code.OP_F64_CONST
    (by simp [initial, Wasm1.Loop.initial])
    (read_at f64Bytes initial 1#usize code.OP_F64_CONST (by decide) rfl
      (by simp [f64Bytes, bytes, initial, Wasm1.Loop.initial, code.OP_F64_CONST, alloc.vec.Vec.deref])) hstep]
  rw [loop_step_with recorder f64Bytes env (resultContext .F64) _ _ pushed last finished code.OP_END
    (by simp [hc, first, initial, Wasm1.Loop.initial])
    (read_at f64Bytes pushed 10#usize code.OP_END (by simp [hp, f64Bytes, bytes, alloc.vec.Vec.deref])
      (by simp [hp]) (by simp [hp, f64Bytes, bytes, code.OP_END, alloc.vec.Vec.deref]))
    (step_end f64Bytes env (resultContext .F64) _ last finished .Body (.Value .F64) hend)]
  exact loop_done_with recorder f64Bytes env (resultContext .F64) _ finished hfc hfp

open Examples.Wasm1Body in
/-- The closing body end is observed before the driver rejects trailing bytes. -/
theorem trailing_bytes_after_end_trace (env : module.Env) :
    ∃ finished, code.validate_body_with recorder trailingBytes env emptyContext [] =
      .ok (.Err .TrailingBytes, [observation finished (.end_ .Body .Empty)]) := by
  let st := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  obtain ⟨⟨_, finished⟩, hend, rfl, hc, hv, hp⟩ := WP.spec_imp_exists
    (code.read_end.empty st [] ⟨.Body, .Empty, Control.signature (.Empty), 0#usize, false⟩ rfl rfl rfl)
  dsimp only at hc hv hp
  refine ⟨finished, ?_⟩
  apply public_of_loop_with recorder trailingBytes env emptyContext .Empty (.Err .TrailingBytes) [] _
    (by simp [trailingBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step_with recorder trailingBytes env emptyContext [] _ (Wasm1.Loop.initial .Empty) st finished code.OP_END
    (by simp [Wasm1.Loop.initial])
    (read_at trailingBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_END (by decide) rfl
      (by simp [trailingBytes, Wasm1.Loop.initial, code.OP_END, alloc.vec.Vec.deref]))
    (step_end trailingBytes env emptyContext [] st finished .Body .Empty hend)]
  apply loop_trailing_with recorder trailingBytes env emptyContext _ finished hc
  simp [hp, st, trailingBytes, alloc.vec.Vec.deref]

open Examples.Wasm1Body in
/-- Rejecting the first NOP callback stops before the otherwise valid final end. -/
theorem rejecting_first_hook_stops (env : module.Env) :
    code.validate_body_with (rejectAt 0 .OutOfMemory) nopBytes env emptyContext [] =
      .ok (.Err (.Visitor .OutOfMemory),
        [⟨.op {Wasm1.Loop.initial .Empty with pos := 1#usize} .nop, .Err .OutOfMemory⟩]) := by
  let st := { Wasm1.Loop.initial .Empty with pos := 1#usize }
  apply public_of_loop_with (rejectAt 0 .OutOfMemory) nopBytes env emptyContext .Empty
    (.Err (.Visitor .OutOfMemory)) [] _
    (by simp [nopBytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  apply loop_error_with (rejectAt 0 .OutOfMemory) nopBytes env emptyContext [] _
    (Wasm1.Loop.initial .Empty) st st code.OP_NOP (.Visitor .OutOfMemory)
    (by simp [Wasm1.Loop.initial])
    (read_at nopBytes (Wasm1.Loop.initial .Empty) 1#usize code.OP_NOP (by decide) rfl
      (by simp [nopBytes, Wasm1.Loop.initial, code.OP_NOP, alloc.vec.Vec.deref]))
  simp [st, rejectAt, ofHandler, code.visit,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

private def frame (kind : code.LabelKind) : code.Ctrl := ⟨kind, .Empty, Control.signature (.Empty), 0#usize, false⟩

private def state (pos : Usize) (frames : List code.Ctrl) (vals : List code.StackType := [])
    (hc : frames.length ≤ 8 := by decide) (hv : vals.length ≤ 8 := by decide) : code.OpIterState :=
  ⟨alloc.vec.Vec.from vals (by scalar_tac), alloc.vec.Vec.from frames (by scalar_tac), pos⟩

private theorem state_ext (s t : code.OpIterState)
    (hv : s.vals.val = t.vals.val) (hc : s.ctrls.val = t.ctrls.val) (hp : s.pos = t.pos) : s = t := by
  have hv' := alloc.vec.Vec.ext _ _ hv
  have hc' := alloc.vec.Vec.ext _ _ hc
  cases s
  cases t
  simp_all

private theorem read_block_empty (st out : code.OpIterState) (data : Slice U8) (next : Usize)
    (hb : Wasm1.BytesAt data st.pos [0x40#u8] next)
    (hcap : st.ctrls.val.length < Usize.max)
    (hv : out.vals.val = st.vals.val)
    (hc : out.ctrls.val = st.ctrls.val ++ [Control.frame st .Block .Empty])
    (hp : out.pos = next) : code.read_block st data = .ok (.Ok .Empty, out) := by
  obtain ⟨⟨_, s⟩, hr, rfl, hspos, hsvals, hsctrls⟩ := WP.spec_imp_exists
    (code.read_block.complete st data .Empty next hb hcap trivial)
  dsimp only at hspos hsvals hsctrls
  have heq : s = out := state_ext _ _ (by simpa [hsvals] using hv.symm)
    (hsctrls.trans hc.symm) (hspos.trans hp.symm)
  simpa [heq] using hr

private theorem read_if_empty (st out : code.OpIterState) (data : Slice U8) (next : Usize)
    (hb : Wasm1.BytesAt data st.pos [0x40#u8] next)
    (hcap : st.ctrls.val.length < Usize.max)
    (hvs : st.vals.val = [.Val .I32]) (hbase : (Control.base st).val = 0)
    (hv : out.vals.val = []) (hc : out.ctrls.val = st.ctrls.val ++ [frame .Then])
    (hp : out.pos = next) : code.read_if st data = .ok (.Ok .Empty, out) := by
  have ht : Sequence.Realizes (Control.polymorphic st) [.Val .I32] ([] ++ [.I32]) :=
    Sequence.realizes_default _ _
  obtain ⟨⟨_, s⟩, hr, rfl, hspos, rest, hvs', _, hcs', ht'⟩ := WP.spec_imp_exists
    (code.read_if.complete st data .Empty next [] [.Val .I32] [] hb hvs hbase hcap ht trivial)
  have hnil := ht'.empty_values
  dsimp only at hspos hvs' hcs'
  have hsv : s.vals.val = [] := by simpa [hnil] using hvs'
  have hlen : alloc.vec.Vec.len s.vals = 0#usize := by scalar_tac
  have hsc : s.ctrls.val = st.ctrls.val ++ [frame .Then] := by
    simpa [Control.frame, hlen, frame] using hcs'
  have heq : s = out := state_ext _ _ (hsv.trans hv.symm) (hsc.trans hc.symm) (hspos.trans hp.symm)
  simpa [heq] using hr

private theorem read_end_empty (st out : code.OpIterState) (parents : List code.Ctrl)
    (kind : code.LabelKind) (hcs : st.ctrls.val = parents ++ [frame kind])
    (hvs : st.vals.val = []) (hv : out.vals.val = []) (hc : out.ctrls.val = parents)
    (hp : out.pos = st.pos) : code.read_end st = .ok (.Ok (kind, .Empty), out) := by
  obtain ⟨⟨_, s⟩, hr, rfl, hsc, hsv, hsp⟩ := WP.spec_imp_exists
    (code.read_end.empty st parents (frame kind) hcs rfl (by simp [hvs, frame]))
  dsimp only at hsc hsv hsp
  have heq : s = out := state_ext _ _ (by simpa [hsv, hvs] using hv.symm)
    (hsc.trans hc.symm) (hsp.trans hp.symm)
  simpa [heq, frame] using hr

private theorem read_else_empty (st out : code.OpIterState) (parents : List code.Ctrl)
    (hcs : st.ctrls.val = parents ++ [frame .Then])
    (hvs : st.vals.val = []) (hv : out.vals.val = [])
    (hc : out.ctrls.val = parents ++ [frame .Else]) (hp : out.pos = st.pos) :
    code.read_else st = .ok (.Ok .Empty, out) := by
  obtain ⟨⟨_, s⟩, hr, rfl, hsc, hsv, hsp⟩ := WP.spec_imp_exists
    (code.read_else.complete st parents (frame .Then) [] [] hcs hvs rfl rfl
      (Sequence.realizes_default _ _))
  dsimp only at hsc hsv hsp
  have heq : s = out := state_ext _ _ (by simpa using hsv.trans hv.symm)
    (by simpa [frame] using hsc.trans hc.symm) (hsp.trans hp.symm)
  simpa [heq, frame] using hr

private theorem read_one (st out : code.OpIterState) (data : Slice U8) (next : Usize)
    (hb : SignedLeb32.Decoded data st.pos (1#i32).val next)
    (hcap : st.vals.val.length < Usize.max)
    (hv : out.vals.val = st.vals.val ++ [.Val .I32]) (hc : out.ctrls = st.ctrls)
    (hp : out.pos = next) : code.read_i32_const st data = .ok (.Ok 1#i32, out) := by
  have hd := reader.read_s32_leb.complete data st.pos 1#i32 next hb
  obtain ⟨⟨_, s⟩, hr, rfl, hsv, hsc, hsp⟩ := WP.spec_imp_exists
    (code.read_i32_const.from_read st data 1#i32 next hd hcap)
  dsimp only at hsv hsc hsp
  have heq : s = out := state_ext _ _ (hsv.trans hv.symm)
    (by simp [hsc, hc]) (hsp.trans hp.symm)
  simpa [heq] using hr



def bareIfBytes : Slice U8 := bytes
  [2#u8, 64#u8, 65#u8, 1#u8, 4#u8, 64#u8, 1#u8, 11#u8, 11#u8, 11#u8]

/-- Exact public callback order for nested block and a bare if with no synthetic else callback. -/
theorem nested_bare_if_trace (env : module.Env) :
    ∃ s2 s4 s6 s7 s8 s9 s10,
      code.validate_body_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [] =
        .ok (.Ok (), [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty), observation s9 (.end_ .Block .Empty), observation s10 (.end_ .Body .Empty)]) := by
  let s0 := Wasm1.Loop.initial .Empty
  let s2 := state 2#usize [frame .Body, frame .Block]
  let s4 := state 4#usize [frame .Body, frame .Block] [.Val .I32]
  let s6 := state 6#usize [frame .Body, frame .Block, frame .Then]
  let s7 := state 7#usize [frame .Body, frame .Block, frame .Then]
  let s8 := state 8#usize [frame .Body, frame .Block]
  let s9 := state 9#usize [frame .Body]
  let s10 := state 10#usize []
  have hb : code.read_block {s0 with pos := 1#usize} bareIfBytes = .ok (.Ok .Empty, s2) := by
    apply read_block_empty _ _ _ 2#usize
      ⟨rfl, rfl, by decide⟩ (by simp [s0, Wasm1.Loop.initial]; scalar_tac)
      (by rfl) (by with_unfolding_all rfl) rfl
  have hon : SignedLeb32.Decoded bareIfBytes 3#usize (1#i32).val 4#usize := by
    refine ⟨[1#u8], rfl, rfl, by decide, [], 1#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  have hconst : code.read_i32_const {s2 with pos := 3#usize} bareIfBytes = .ok (.Ok 1#i32, s4) := by
    exact read_one _ _ _ _ hon (by simp [s2, state]; scalar_tac) rfl rfl rfl
  have hif : code.read_if {s4 with pos := 5#usize} bareIfBytes = .ok (.Ok .Empty, s6) := by
    exact read_if_empty _ _ _ 6#usize ⟨rfl, rfl, by decide⟩
      (by simp [s4, state]; scalar_tac) rfl (by simp [Control.base, s4, state, frame]) rfl rfl rfl
  have he8 : code.read_end {s7 with pos := 8#usize} = .ok (.Ok (.Then, .Empty), s8) := by
    exact read_end_empty _ _ [frame .Body, frame .Block] .Then rfl rfl rfl rfl rfl
  have he9 : code.read_end {s8 with pos := 9#usize} = .ok (.Ok (.Block, .Empty), s9) := by
    exact read_end_empty _ _ [frame .Body] .Block rfl rfl rfl rfl rfl
  have he10 : code.read_end {s9 with pos := 10#usize} = .ok (.Ok (.Body, .Empty), s10) := by
    exact read_end_empty _ _ [] .Body rfl rfl rfl rfl rfl
  refine ⟨s2, s4, s6, s7, s8, s9, s10, ?_⟩
  apply public_of_loop_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext .Empty (.Ok ()) [] _
    (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [] [observation s2 (.block .Empty)]
    s0 {s0 with pos := 1#usize} s2 code.OP_BLOCK
    (by simp [s0, Wasm1.Loop.initial])
    (read_at bareIfBytes s0 1#usize code.OP_BLOCK (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s0, Wasm1.Loop.initial, global_simps]))
    (by simp [hb, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32)]
    s2 {s2 with pos := 3#usize} s4 code.OP_I32_CONST
    (by simp [s2, state])
    (read_at bareIfBytes s2 3#usize code.OP_I32_CONST (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s2, state, global_simps]))
    (by simp [hconst, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty)]
    s4 {s4 with pos := 5#usize} s6 code.OP_IF
    (by simp [s4, state])
    (read_at bareIfBytes s4 5#usize code.OP_IF (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s4, state, global_simps]))
    (by simp [hif, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop)]
    s6 {s6 with pos := 7#usize} s7 code.OP_NOP
    (by simp [s6, state])
    (read_at bareIfBytes s6 7#usize code.OP_NOP (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s6, state, global_simps]))
    (by simp [recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch, s6, s7, state])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty)]
    s7 {s7 with pos := 8#usize} s8 code.OP_END
    (by simp [s7, state])
    (read_at bareIfBytes s7 8#usize code.OP_END (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s7, state, global_simps]))
    (by simp [he8, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty), observation s9 (.end_ .Block .Empty)]
    s8 {s8 with pos := 9#usize} s9 code.OP_END
    (by simp [s8, state])
    (read_at bareIfBytes s8 9#usize code.OP_END (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s8, state, global_simps]))
    (by simp [he9, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty), observation s9 (.end_ .Block .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.end_ .Then .Empty), observation s9 (.end_ .Block .Empty), observation s10 (.end_ .Body .Empty)]
    s9 {s9 with pos := 10#usize} s10 code.OP_END
    (by simp [s9, state])
    (read_at bareIfBytes s9 10#usize code.OP_END (by decide) rfl
      (by simp [bareIfBytes, bytes, alloc.vec.Vec.deref, s9, state, global_simps]))
    (by simp [he10, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  exact loop_done_with recorder bareIfBytes env Examples.Wasm1Body.emptyContext _ s10 rfl rfl

def elseIfBytes : Slice U8 := bytes
  [2#u8, 64#u8, 65#u8, 1#u8, 4#u8, 64#u8, 1#u8, 5#u8, 1#u8, 11#u8, 11#u8, 11#u8]

/-- Exact public callback order for nested block and an explicit else. -/
theorem nested_else_if_trace (env : module.Env) :
    ∃ s2 s4 s6 s7 s8 s9 s10 s11 s12,
      code.validate_body_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [] =
        .ok (.Ok (), [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty), observation s11 (.end_ .Block .Empty), observation s12 (.end_ .Body .Empty)]) := by
  let s0 := Wasm1.Loop.initial .Empty
  let s2 := state 2#usize [frame .Body, frame .Block]
  let s4 := state 4#usize [frame .Body, frame .Block] [.Val .I32]
  let s6 := state 6#usize [frame .Body, frame .Block, frame .Then]
  let s7 := state 7#usize [frame .Body, frame .Block, frame .Then]
  let s8 := state 8#usize [frame .Body, frame .Block, frame .Else]
  let s9 := state 9#usize [frame .Body, frame .Block, frame .Else]
  let s10 := state 10#usize [frame .Body, frame .Block]
  let s11 := state 11#usize [frame .Body]
  let s12 := state 12#usize []
  have hb : code.read_block {s0 with pos := 1#usize} elseIfBytes = .ok (.Ok .Empty, s2) := by
    apply read_block_empty _ _ _ 2#usize
      ⟨rfl, rfl, by decide⟩ (by simp [s0, Wasm1.Loop.initial]; scalar_tac)
      (by rfl) (by with_unfolding_all rfl) rfl
  have hon : SignedLeb32.Decoded elseIfBytes 3#usize (1#i32).val 4#usize := by
    refine ⟨[1#u8], rfl, rfl, by decide, [], 1#u8, rfl, by decide,
      by simp, by decide, ?_, by decide, by decide⟩
    norm_num [SignedLeb.finalValue, Leb128.payload]
  have hconst : code.read_i32_const {s2 with pos := 3#usize} elseIfBytes = .ok (.Ok 1#i32, s4) := by
    exact read_one _ _ _ _ hon (by simp [s2, state]; scalar_tac) rfl rfl rfl
  have hif : code.read_if {s4 with pos := 5#usize} elseIfBytes = .ok (.Ok .Empty, s6) := by
    exact read_if_empty _ _ _ 6#usize ⟨rfl, rfl, by decide⟩
      (by simp [s4, state]; scalar_tac) rfl (by simp [Control.base, s4, state, frame]) rfl rfl rfl
  have hel : code.read_else {s7 with pos := 8#usize} = .ok (.Ok .Empty, s8) := by
    exact read_else_empty _ _ [frame .Body, frame .Block] rfl rfl rfl rfl rfl
  have he10 : code.read_end {s9 with pos := 10#usize} = .ok (.Ok (.Else, .Empty), s10) := by
    exact read_end_empty _ _ [frame .Body, frame .Block] .Else rfl rfl rfl rfl rfl
  have he11 : code.read_end {s10 with pos := 11#usize} = .ok (.Ok (.Block, .Empty), s11) := by
    exact read_end_empty _ _ [frame .Body] .Block rfl rfl rfl rfl rfl
  have he12 : code.read_end {s11 with pos := 12#usize} = .ok (.Ok (.Body, .Empty), s12) := by
    exact read_end_empty _ _ [] .Body rfl rfl rfl rfl rfl
  refine ⟨s2, s4, s6, s7, s8, s9, s10, s11, s12, ?_⟩
  apply public_of_loop_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext .Empty (.Ok ()) [] _
    (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, limits.MAX_FUNCTION_BYTES]) rfl
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [] [observation s2 (.block .Empty)]
    s0 {s0 with pos := 1#usize} s2 code.OP_BLOCK
    (by simp [s0, Wasm1.Loop.initial])
    (read_at elseIfBytes s0 1#usize code.OP_BLOCK (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s0, Wasm1.Loop.initial, global_simps]))
    (by simp [hb, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32)]
    s2 {s2 with pos := 3#usize} s4 code.OP_I32_CONST
    (by simp [s2, state])
    (read_at elseIfBytes s2 3#usize code.OP_I32_CONST (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s2, state, global_simps]))
    (by simp [hconst, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty)]
    s4 {s4 with pos := 5#usize} s6 code.OP_IF
    (by simp [s4, state])
    (read_at elseIfBytes s4 5#usize code.OP_IF (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s4, state, global_simps]))
    (by simp [hif, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop)]
    s6 {s6 with pos := 7#usize} s7 code.OP_NOP
    (by simp [s6, state])
    (read_at elseIfBytes s6 7#usize code.OP_NOP (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s6, state, global_simps]))
    (by simp [recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch, s6, s7, state])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty)]
    s7 {s7 with pos := 8#usize} s8 code.OP_ELSE
    (by simp [s7, state])
    (read_at elseIfBytes s7 8#usize code.OP_ELSE (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s7, state, global_simps]))
    (by simp [hel, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop)]
    s8 {s8 with pos := 9#usize} s9 code.OP_NOP
    (by simp [s8, state])
    (read_at elseIfBytes s8 9#usize code.OP_NOP (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s8, state, global_simps]))
    (by simp [recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch, s8, s9, state])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty)]
    s9 {s9 with pos := 10#usize} s10 code.OP_END
    (by simp [s9, state])
    (read_at elseIfBytes s9 10#usize code.OP_END (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s9, state, global_simps]))
    (by simp [he10, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty), observation s11 (.end_ .Block .Empty)]
    s10 {s10 with pos := 11#usize} s11 code.OP_END
    (by simp [s10, state])
    (read_at elseIfBytes s10 11#usize code.OP_END (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s10, state, global_simps]))
    (by simp [he11, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  rw [loop_step_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty), observation s11 (.end_ .Block .Empty)] [observation s2 (.block .Empty), observation s4 (.i32_const 1#i32), observation s6 (.if_ .Empty), observation s7 (.nop), observation s8 (.else_ .Empty), observation s9 (.nop), observation s10 (.end_ .Else .Empty), observation s11 (.end_ .Block .Empty), observation s12 (.end_ .Body .Empty)]
    s11 {s11 with pos := 12#usize} s12 code.OP_END
    (by simp [s11, state])
    (read_at elseIfBytes s11 12#usize code.OP_END (by decide) rfl
      (by simp [elseIfBytes, bytes, alloc.vec.Vec.deref, s11, state, global_simps]))
    (by simp [he12, recorder, ofHandler, observation, code.visit, core.result.Result.Insts.CoreOpsTry.branch])]
  exact loop_done_with recorder elseIfBytes env Examples.Wasm1Body.emptyContext _ s12 rfl rfl

end Itasca.Examples.Wasm1VisitorTrace
