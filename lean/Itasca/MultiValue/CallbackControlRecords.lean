import Itasca.MultiValue.CallbackControlBytes

open Aeneas Aeneas.Std

namespace Itasca

attribute [local step] code.pop_with_type.total code.check_suffix.spec

/-- Call stack adjustment retains the exact encoded function index. -/
theorem code.call_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (hs : Control.Shape st.core) :
    code.call_info st data env ⦃ r => ∀ index, r.1 = .Ok index →
      Leb128.Decoded data st.core.pos index r.2.core.pos ⦄ := by
  unfold code.call_info
  step with code.take_index.spec st.core data as ⟨r, s, hv, hc, hd⟩
  have hs' : Control.Shape s :=
    ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
  cases r <;> step* <;> simp_all

/-- Indirect-call callbacks retain both independently decoded indices. -/
theorem code.call_indirect_info.bytes (st : code.BodyState) (data : Slice U8)
    (env : module.Env) (hs : Control.Shape st.core) :
    code.call_indirect_info st data env ⦃ r => ∀ index table, r.1 = .Ok (index, table) →
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
    step with code.take_index.spec s data as ⟨r, s', hv', hc', hd'⟩
    have hs'' : Control.Shape s' :=
      ⟨by simpa [hc'] using hs'.ordered, by simpa [hc', hv'] using hs'.bounded⟩
    cases r with
    | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok table =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step* <;> simp_all
      cases r2 with
      | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok value =>
        simp only [bind_ok]
        step* <;> simp_all
        cases r3 with
        | Err e => simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          simp only [bind_ok, WP.spec_ok]
          intro idx tab equal
          obtain ⟨rfl, rfl⟩ := (core.result.Result.Ok.inj equal)
          exact ⟨s.pos, hd, by simpa only [r3_post2] using hd'⟩

end Itasca

namespace Itasca.MultiValue.CallbackTrace

open VisitorTrace

/-- Exact bytes for an actual profile-dispatched control step. -/
def ProfileStepRecords {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (ctx : code.Context) (opcode : U8) : Prop :=
  ∀ v result final v', code.step_profile visitor st data env ctx index .Wasm2 opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final.core

theorem step_block {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x02#u8) :
    ProfileStepRecords p visitor observe ctx 0x02#u8 := by
  intro v result final v' run
  rw [dispatch_block] at run
  apply bodyRun.trace data p.start _ visitor observe records .block ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := Body.byte_limit_room
    omega
  have spec := code.enter_info.bytes st data env .Block p.opened.shape.core
    p.opened.shape.aligned capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.block bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .block h) (spec bt rfl)⟩

theorem step_loop {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x03#u8) :
    ProfileStepRecords p visitor observe ctx 0x03#u8 := by
  intro v result final v' run
  rw [dispatch_loop] at run
  apply bodyRun.trace data p.start _ visitor observe records .loop ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := Body.byte_limit_room
    omega
  have spec := code.enter_info.bytes st data env .Loop p.opened.shape.core
    p.opened.shape.aligned capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.loop bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .loop h) (spec bt rfl)⟩

theorem step_if {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x04#u8) :
    ProfileStepRecords p visitor observe ctx 0x04#u8 := by
  intro v result final v' run
  rw [dispatch_if] at run
  apply bodyRun.trace data p.start _ visitor observe records .if_ ?_ v result final v' run
  intro state bt hr
  have capacity : st.blocks.val.length < Usize.max := by
    have := p.ctrls; have := p.inbounds; have := p.size; have := Body.byte_limit_room
    omega
  have spec := code.enter_info.bytes st data env .Then p.opened.shape.core
    p.opened.shape.aligned capacity
  rw [hr, WP.spec_ok] at spec
  exact ⟨.if_ bt, rfl, by simp [Action.opcode],
    At.of_block_type bt p.inbounds byte p.pos (fun _ h => .if_ h) (spec bt rfl)⟩

theorem step_else {data env locals index st} (p : Pending data env locals index st)
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
  simpa [pos] using Wasm.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_end {data env locals index st} (p : Pending data env locals index st)
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
  simpa [pos] using Wasm.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega)

theorem step_br {data env locals index st} (p : Pending data env locals index st)
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
    At.plain (Wasm.At.of_u32 depth p.inbounds byte p.pos (fun _ => .br depth) (spec depth types rfl))⟩

theorem step_br_if {data env locals index st} (p : Pending data env locals index st)
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
    At.plain (Wasm.At.of_u32 depth p.inbounds byte p.pos (fun _ => .brIf depth) (spec depth types rfl))⟩

theorem step_call {data env locals index st} (p : Pending data env locals index st)
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
    At.plain (Wasm.At.of_u32 idx p.inbounds byte p.pos (fun _ => .call idx) (spec idx rfl))⟩

theorem step_call_indirect {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x11#u8) :
    ProfileStepRecords p visitor observe ctx 0x11#u8 := by
  intro v result final v' run
  rw [dispatch_call_indirect] at run
  apply bodyRun.trace data p.start _ visitor observe records
    (fun a : U32 × U32 => .call_indirect a.1 a.2) ?_ v result final v' run
  rintro state ⟨idx, table⟩ hr
  have spec := code.call_indirect_info.bytes st data env p.opened.shape.core
  rw [hr, WP.spec_ok] at spec
  obtain ⟨middle, hidx, htable⟩ := spec idx table rfl
  obtain ⟨typeBytes, hs, hl, hb, he⟩ := hidx
  obtain ⟨tableBytes, hs', hl', hb', he'⟩ := htable
  exact ⟨.plain (.CALL_INDIRECT (.mk_uN table.val) (.mk_uN idx.val)), rfl,
    by simp [Action.opcode], At.of_immediate p.inbounds byte p.pos
      (.reference (.callIndirect idx table he he'))
      ((show Wasm.BytesAt data st.core.pos typeBytes middle from ⟨hs, hl, hb⟩).append ⟨hs', hl', hb'⟩)⟩

end Itasca.MultiValue.CallbackTrace
