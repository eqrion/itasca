import Itasca.Wasm2.Trace.ControlBytes
import Itasca.Wasm2.Control.Return

/-!
# Callback byte provenance for control instructions

`ProfileStepRecords` states the exact callback trace of one control step of `code.step_profile`. `step_block`, `step_loop`, `step_if`, `step_else`, `step_end`, `step_br`,
`step_br_if`, `step_return`, `step_call` and `step_call_indirect` prove it for each control
opcode except `br_table`, which is in `Wasm2/Trace/TableBytes`.
-/

open Aeneas Aeneas.Std

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

/-- Call stack adjustment returns the exact encoded function index. -/
theorem code.call_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (hs : Control.Shape st.core) :
    code.call_info st data env ⦃ r => ∀ index, r.1 = .Ok index →
      Leb128.Decoded data st.core.pos index r.2.core.pos ⦄ := by
  unfold code.call_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
  have hs' : Control.Shape s :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r <;> step*; simp_all

/-- Indirect-call callbacks receive both independently decoded indices. -/
theorem code.call_indirect_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (profile : ValidationProfile) (hs : Control.Shape st.core) :
    code.call_indirect_info st data env profile ⦃ r => ∀ index table, r.1 = .Ok (index, table) →
      ∃ middle, Leb128.Decoded data st.core.pos index middle ∧
        Leb128.Decoded data middle table r.2.core.pos ⦄ := by
  unfold code.call_indirect_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
  have hs' : Control.Shape s :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r with
  | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok index =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨rb, hrb, _⟩ := WP.spec_imp_exists (code.check_table_byte.spec profile data s.pos)
    rw [hrb]
    cases rb with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok u =>
    simp only [bind_ok]
    step with code.take_index.spec s data as ⟨r, s', hv', hc', hd'⟩
    have hs'' : Control.Shape s' :=
      ⟨by simpa [hc'] using hs'.ordered, by simpa [hc', hv'] using hs'.bounded⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok table =>
      simp only [bind_ok]
      step*
      simp_all
      cases r3 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [bind_ok]
        step*
        simp_all
        cases r4 with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          simp only [bind_ok, WP.spec_ok]
          intro idx tab equal
          obtain ⟨rfl, rfl⟩ := (core.result.Result.Ok.inj equal)
          exact ⟨s.pos, hd, by simpa only [r4_post2] using hd'⟩

end Itasca

namespace Itasca.Wasm2.CallbackTrace

open VisitorTrace

/-- Exact bytes for an actual profile-dispatched control step. -/
def ProfileStepRecords {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (ctx : code.Context) (opcode : U8) : Prop :=
  ∀ v result final v', code.step_profile visitor st data env ctx index profile opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final.core

theorem step_block {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x02#u8) :
    ProfileStepRecords p visitor observe ctx 0x02#u8 := by
  intro v result final v' run
  rw [dispatch_block] at run
  apply bodyRun.trace data p.start _ visitor observe records .block ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env profile .Block p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.block bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .block h) (spec bt rfl)⟩

theorem step_loop {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x03#u8) :
    ProfileStepRecords p visitor observe ctx 0x03#u8 := by
  intro v result final v' run
  rw [dispatch_loop] at run
  apply bodyRun.trace data p.start _ visitor observe records .loop ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env profile .Loop p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.loop bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .loop h) (spec bt rfl)⟩

theorem step_if {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x04#u8) :
    ProfileStepRecords p visitor observe ctx 0x04#u8 := by
  intro v result final v' run
  rw [dispatch_if] at run
  apply bodyRun.trace data p.start _ visitor observe records .if_ ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := limits.MAX_FUNCTION_BYTES.room
    omega
  have spec := code.enter_info.bytes st data env profile .Then p.opened.shape.core capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.if_ bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .if_ h) (spec bt rfl)⟩

theorem step_else {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x05#u8) :
    ProfileStepRecords p visitor observe ctx 0x05#u8 := by
  intro v result final v' run
  rw [dispatch_else] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun a : code.LabelKind × signature.BlockType => .else_ a.2) ?_ v result final v' run
  intro state pair hr
  have spec := code.end_frame_info.total st env true p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  have pos : state.core.pos = st.core.pos := spec.2.2.2
  refine ⟨.else_, rfl, by simp [Action.opcode], ?_⟩
  apply At.of_immediate p.inbounds byte p.pos .else_
  simpa [pos] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_end {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8) :
    ProfileStepRecords p visitor observe ctx 0x0b#u8 := by
  intro v result final v' run
  rw [dispatch_end] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun a : code.LabelKind × signature.BlockType => .end_ a.1 a.2) ?_ v result final v' run
  intro state pair hr
  have spec := code.end_frame_info.total st env false p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  have pos : state.core.pos = st.core.pos := spec.2.2.2
  refine ⟨.end_, rfl, by simp [Action.opcode], ?_⟩
  apply At.of_immediate p.inbounds byte p.pos .end_
  simpa [pos] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_br {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0c#u8) :
    ProfileStepRecords p visitor observe ctx 0x0c#u8 := by
  intro v result final v' run
  rw [dispatch_br] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × signature.ResultType => .br a.1 a.2) ?_ v result final v' run
  rintro state ⟨depth, types⟩ hr
  have spec := code.branch_info.bytes st data env false p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.BR (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 depth p.inbounds byte p.pos (fun _ => .br depth) (spec depth types rfl))⟩

theorem step_br_if {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0d#u8) :
    ProfileStepRecords p visitor observe ctx 0x0d#u8 := by
  intro v result final v' run
  rw [dispatch_br_if] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × signature.ResultType => .br_if a.1 a.2) ?_ v result final v' run
  rintro state ⟨depth, types⟩ hr
  have spec := code.branch_info.bytes st data env true p.opened.shape.core p.opened.shape.aligned
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.BR_IF (.mk_uN depth.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 depth p.inbounds byte p.pos (fun _ => .brIf depth) (spec depth types rfl))⟩

theorem step_call {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x10#u8) :
    ProfileStepRecords p visitor observe ctx 0x10#u8 := by
  intro v result final v' run
  rw [dispatch_call] at run
  apply bodyRun.trace data p.start _ visitor observe records .call ?_ v result final v' run
  intro state idx hr
  have spec := code.call_info.bytes st data env p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  exact ⟨.plain (.CALL (.mk_uN idx.val)), rfl, by simp [Action.opcode],
    At.plain (Wasm1.At.of_u32 idx p.inbounds byte p.pos (fun _ => .call idx) (spec idx rfl))⟩

theorem step_call_indirect {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    ProfileStepRecords p visitor observe ctx 0x11#u8 := by
  intro v result final v' run
  rw [dispatch_call_indirect] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × U32 => .call_indirect a.1 a.2) ?_ v result final v' run
  rintro state ⟨idx, table⟩ hr
  have spec := code.call_indirect_info.bytes st data env profile p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  obtain ⟨middle, hidx, htable⟩ := spec idx table rfl
  obtain ⟨typeBytes, hs, hl, hb, he⟩ := hidx
  obtain ⟨tableBytes, hs', hl', hb', he'⟩ := htable
  exact ⟨.plain (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)), rfl,
    by simp [Action.opcode], At.of_immediate p.inbounds byte p.pos
      (.reference (.callIndirect idx table he he'))
      ((show Wasm1.BytesAt data st.core.pos typeBytes middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)⟩

end Itasca.Wasm2.CallbackTrace

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackTrace
open VisitorTrace

/-- Factor the actual return callback after result checking and stack erasure. -/
theorem dispatch_return {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (profile : ValidationProfile) (v : V) :
    code.step_profile visitor st data env ctx index profile 0x0f#u8 v =
      bodyRun (returnStep st env index) visitor (fun _ => .return_) v := by
  have hc : code.check_opcode profile 0x0f#u8 = .ok (.Ok ()) :=
    code.check_opcode.complete profile _ (by decide)
  simp [code.step_profile, hc, global_simps, bodyRun, returnStep, Std.bind_assoc, Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch, code.visit,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  congr 1
  funext pair
  obtain ⟨r, s⟩ := pair
  cases r with
  | Err e => simp
  | Ok u =>
    cases u
    simp only [bind_ok, Std.bind_assoc, Std.uncurry]
    congr 1
    funext state
    simp only [invoke]
    congr 1
    funext pair
    obtain ⟨reply, w⟩ := pair
    cases reply <;> simp [hookResult]

/-- Return reads no immediate bytes; checking results and erasing the active
stack segment preserve its post-opcode cursor. -/
theorem return_position (st : code.BodyState) (env : module.Env) (index : U32)
    (shape : Control.Shape st.core) :
    returnStep st env index ⦃ r => r.2.core.pos = st.core.pos ⦄ := by
  obtain ⟨⟨res, popped⟩, hp, hs, _, hpos, _⟩ := WP.spec_imp_exists
    (code.pop_results.total st.core env (.Type index .Results) shape)
  dsimp only at hs hpos
  cases res with
  | Err e => simpa [returnStep, hp] using hpos
  | Ok u =>
    cases u
    obtain ⟨marked, hm, _, _, hmark, _⟩ := WP.spec_imp_exists
      (code.mark_unreachable_total popped hs)
    simpa [returnStep, hp, hm] using hmark.trans hpos

theorem step_return {data env profile locals index st} (p : Pending data env profile locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0f#u8) :
    ProfileStepRecords p visitor observe ctx 0x0f#u8 := by
  intro v result final v' run
  rw [dispatch_return] at run
  apply bodyRun.trace data p.start _ visitor observe records (fun _ => .return_) ?_ v result final v' run
  intro state _ hr
  have spec := return_position st env index p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  refine ⟨.plain .RETURN, rfl, by simp [Action.opcode], ?_⟩
  exact At.plain (.no_immediate p.inbounds byte (by simpa [spec] using p.pos) .return_)

end Itasca.Wasm2.CallbackTrace
