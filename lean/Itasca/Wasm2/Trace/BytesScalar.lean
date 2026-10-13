import Itasca.Wasm2.Trace.Bytes
import Itasca.Wasm2.Scalar.Step
import Itasca.Wasm2.NumericExt.Dispatch
import Itasca.Visitor.EventDispatch

/-!
Independent byte provenance for inherited scalar and numeric-extension callbacks.
The reader lemmas operate on the Core 2.0 control zipper. Callback rejection is
retained, and an undecodable instruction contributes no operator callback.
-/

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.CallbackBytes

open VisitorTrace CallbackTrace

/-- The inherited scalar dispatcher records independently decoded Core 2.0 tokens. -/
def BaseRecords {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (opcode : U8) : Prop :=
  ∀ v result final v', code.step visitor st.core data env ⟨locals, p.ft.results⟩ opcode v =
      .ok (result, final, v') →
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final

theorem step_nop {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (_capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_NOP) :
    BaseRecords p visitor observe code.OP_NOP := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_nop] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (fun _ => .nop) ?_ v result final v' h
  intro s a hr
  have heq : st.core = s := by simpa using hr
  subst s
  exact ⟨.plain .NOP, rfl, by simp only [Action.opcode]; decide,
    .plain (.no_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos .nop)⟩

theorem step_i32_const {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I32_CONST) :
    BaseRecords p visitor observe code.OP_I32_CONST := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_i32_const] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .i32_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_i32_const.spec st.core data (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (Core.i32Const a), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_s32 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1)⟩

theorem step_i64_const {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_I64_CONST) :
    BaseRecords p visitor observe code.OP_I64_CONST := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_i64_const] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .i64_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_i64_const.spec st.core data (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.i64 a), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_s64 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1)⟩

theorem step_f32_const {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F32_CONST) :
    BaseRecords p visitor observe code.OP_F32_CONST := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_f32_const] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .f32_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_f32_const.spec st.core data (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.f32 a), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_f32 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1)⟩

theorem step_f64_const {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_F64_CONST) :
    BaseRecords p visitor observe code.OP_F64_CONST := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_f64_const] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .f64_const ?_ v result final v' h
  intro s a hr
  have hs := code.read_f64_const.spec st.core data (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (ScalarConst.f64 a), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_f64 a p.inbounds (by simpa [global_simps] using hbyte) p.pos hs.2.1)⟩

theorem step_drop {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (_capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_DROP) :
    BaseRecords p visitor observe code.OP_DROP := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_drop] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .drop ?_ v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have hs := code.pop_stack_type.segment st.core outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
  change code.pop_stack_type st.core = .ok (.Ok a, s) at hr
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain .DROP, rfl, by simp only [Action.opcode]; decide,
    .plain (.no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hs.2.1] using p.pos) .drop)⟩

theorem step_select {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_SELECT) :
    BaseRecords p visitor observe code.OP_SELECT := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_select] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .select ?_ v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have hs := code.read_select.segment st.core outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  exact ⟨.plain (.SELECT none), rfl, by simp only [Action.opcode]; decide,
    .plain (.no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hs.2.1] using p.pos) .select)⟩

theorem step_unreachable {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (_capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_UNREACHABLE) :
    BaseRecords p visitor observe code.OP_UNREACHABLE := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_unreachable] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (fun _ => .unreachable) ?_
    v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  obtain ⟨s', hm, _, _, _, hp⟩ := WP.spec_imp_exists
    (code.mark_unreachable.spec st.core (p.parents.map Frames.Saved.ctrl) p.current.ctrl ctrls
      (by simp [vals, base]))
  have heq : s' = s := by simpa [code.read_unreachable, hm] using hr
  subst s
  exact ⟨.plain .UNREACHABLE, rfl, by simp only [Action.opcode]; decide,
    .plain (.no_immediate p.inbounds (by simpa [global_simps] using hbyte)
      (by simpa [hp] using p.pos) .unreachable)⟩

theorem step_local_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_GET) :
    BaseRecords p visitor observe code.OP_LOCAL_GET := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_local_get] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .local_get ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_local_get.multi_prefix st.core data env ctx outer p.current.vals vals
    (by have := capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_GET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localGet a encoding) ⟨suffix, length, bound⟩)⟩

theorem step_local_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (_capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_SET) :
    BaseRecords p visitor observe code.OP_LOCAL_SET := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_local_set] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .local_set ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_local_set.multi_prefix st.core data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_SET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localSet a encoding) ⟨suffix, length, bound⟩)⟩

theorem step_local_tee {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_LOCAL_TEE) :
    BaseRecords p visitor observe code.OP_LOCAL_TEE := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_local_tee] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .local_tee ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_local_tee.multi_prefix st.core data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    (by have := capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.LOCAL_TEE (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.localTee a encoding) ⟨suffix, length, bound⟩)⟩

theorem step_global_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_GLOBAL_GET) :
    BaseRecords p visitor observe code.OP_GLOBAL_GET := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_global_get] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .global_get ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_global_get.multi_prefix st.core data env ctx outer p.current.vals vals
    (by have := capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.GLOBAL_GET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.globalGet a encoding) ⟨suffix, length, bound⟩)⟩

theorem step_global_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (_capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_GLOBAL_SET) :
    BaseRecords p visitor observe code.OP_GLOBAL_SET := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_global_set] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords .global_set ?_ v result final v' h
  intro s a hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_global_set.multi_prefix st.core data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨bytes, suffix, length, bound, encoding⟩ := (hs a rfl).1
  exact ⟨.plain (.GLOBAL_SET (.mk_uN a.val)), rfl, by simp only [Action.opcode]; decide,
    .plain (.of_immediate p.inbounds (by simpa [global_simps] using hbyte) p.pos
      (.globalSet a encoding) ⟨suffix, length, bound⟩)⟩

theorem step_memory_size {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_MEMORY_SIZE) :
    BaseRecords p visitor observe code.OP_MEMORY_SIZE := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_memory_size] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (fun _ => .memory_size) ?_ v result final v' h
  intro s a hr
  cases a
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_memory_size.multi_prefix st.core data env ctx outer p.current.vals vals
    (by have := capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hb, hv, hn⟩ := (hs rfl).1
  exact ⟨.plain .MEMORY_SIZE, rfl, by simp only [Action.opcode]; decide,
    .plain (.of_byte 0#u8 p.inbounds (by simpa [global_simps] using hbyte) p.pos .memorySize hb hv hn)⟩

theorem step_memory_grow {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = code.OP_MEMORY_GROW) :
    BaseRecords p visitor observe code.OP_MEMORY_GROW := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  intro v result final v' h
  rw [dispatch_memory_grow] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (fun _ => .memory_grow) ?_ v result final v' h
  intro s a hr
  cases a
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs := code.read_memory_grow.multi_prefix st.core data env ctx outer p.current.vals vals
    (by simp [Control.base, ctrls, base])
    (by have := capacity; omega)
    _ hC p.current.ops (by simpa [hpoly] using typed)
  rw [hr, WP.spec_ok] at hs
  obtain ⟨hb, hv, hn⟩ := (hs rfl).1
  exact ⟨.plain .MEMORY_GROW, rfl, by simp only [Action.opcode]; decide,
    .plain (.of_byte 0#u8 p.inbounds (by simpa [global_simps] using hbyte) p.pos .memoryGrow hb hv hn)⟩

theorem step_numeric {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max) (opcode : U8) (operation : Numeric.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : Numeric.opcodeMeaning opcode = some operation) :
    BaseRecords p visitor observe opcode := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  obtain ⟨hook, hh, hcode, hmeaning⟩ := NumericHook.of_meaning hrow
  intro v result final v' h
  rw [dispatch_numeric visitor st.core data env ctx v opcode operation hook hrow hh] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (fun _ => .numeric hook) ?_
    v result final v' h
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have hs := Numeric.read.segment operation st.core outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) (by have := capacity; omega)
  rw [hr, WP.spec_ok] at hs
  dsimp only at hs
  refine ⟨.plain operation.instruction, by simp only [actionToken, Action.token, hmeaning, Option.map_some, liftToken], ?_,
    .plain (.no_immediate p.inbounds hbyte (by simpa [hs.2.1] using p.pos) (.numeric opcode operation hrow))⟩
  change some hook.opcode ≠ some 0x0E#u8
  intro he
  have hv : opcode.val = 14 := by rw [← hcode, Option.some.inj he]; rfl
  have hb := Numeric.NumericOp.bounds hrow
  omega

theorem step_memory {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max) (opcode : U8) (operation : MemoryMeaning.Operation)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (hrow : MemoryMeaning.opcodeMeaning opcode = some operation) :
    BaseRecords p visitor observe opcode := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  obtain ⟨hook, hh, _, hmeaning⟩ := MemoryHook.of_meaning hrow
  intro v result final v' h
  rw [dispatch_memory visitor st.core data env ctx v opcode operation hook hrow hh] at h
  apply CallbackTrace.run_step_trace data p.start _ visitor observe hrecords (.memory hook) ?_
    v result final v' h
  intro s arg hr
  obtain ⟨C, outer, spine, _, base, typed, ctrls, _, vals⟩ := p.opened
  have hpoly : Control.polymorphic st.core = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic, ctrls]
  have hC : EnvTranslation.Matches env ctx
      (Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ctx)).enter _
  have hs :
      (if operation.store then code.read_store st.core data env operation.ty operation.naturalAlign
        else code.read_load st.core data env operation.ty operation.naturalAlign) ⦃
        Scalar.MemoryPost ((p.current.form.params p.current.ins).map Translate.valueType) data st.core outer p.current.vals
          (Frames.enter C p.current.form p.current.ins p.current.outs) p.current.ops operation.op ⦄ := by
    cases hstore : operation.store with
    | false =>
      simpa only [hstore, Bool.false_eq_true, ↓reduceIte] using
        code.read_load.multi_prefix st.core data env ctx outer p.current.vals vals
          (by simp [Control.base, ctrls, base]) (by have := capacity; omega)
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hstore
    | true =>
      simpa only [hstore, ↓reduceIte] using
        code.read_store.multi_prefix st.core data env ctx outer p.current.vals vals
          (by simp [Control.base, ctrls, base])
          _ hC p.current.ops (by simpa [hpoly] using typed) opcode operation hrow hstore
  rw [hr, WP.spec_ok] at hs
  obtain ⟨middle, ha, ho⟩ := (hs arg rfl).1
  exact ⟨.plain (operation.op arg), by simp only [actionToken, Action.token, hmeaning, Option.map_some, liftToken],
    by cases hook <;> simp only [Action.opcode, MemoryHook.opcode] <;> decide,
    .plain (.of_memory operation arg hrow p.inbounds hbyte p.pos ha ho)⟩


private theorem memory_meaning_exists (opcode : U8)
    (hlo : 0x28 ≤ opcode.val) (hhi : opcode.val ≤ 0x3E) :
    ∃ operation, MemoryMeaning.opcodeMeaning opcode = some operation := by
  rcases opcode with ⟨⟨n, hn⟩⟩
  change 40 ≤ n at hlo
  change n ≤ 62 at hhi
  interval_cases n <;> exact ⟨_, rfl⟩

/-- All inherited scalar byte values, including reserved-opcode rejection. -/
theorem base_scalar_records {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (hrecords : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    BaseRecords p visitor observe opcode := by
  let ctx : code.Context := ⟨locals, p.ft.results⟩
  by_cases hhigh : 0x45 ≤ opcode.val
  · cases hm : Numeric.opcodeMeaning opcode with
    | some operation => exact step_numeric p visitor observe hrecords capacity opcode operation hbyte hm
    | none =>
      intro v result final v' h
      rw [code.step.numeric_dispatch visitor st.core data env ctx opcode v hhigh,
        code.step_numeric.unrecognized visitor st.core opcode v hm] at h
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨[], by simp, .silent _ _ (.empty _)⟩
  by_cases hmemory : 0x28 ≤ opcode.val ∧ opcode.val ≤ 0x3E
  · obtain ⟨operation, hm⟩ := memory_meaning_exists opcode hmemory.1 hmemory.2
    exact step_memory p visitor observe hrecords capacity opcode operation hbyte hm
  by_cases h_nop : opcode = code.OP_NOP
  · rw [h_nop] at hbyte ⊢
    exact step_nop p visitor observe hrecords capacity hbyte
  by_cases h_unreachable : opcode = code.OP_UNREACHABLE
  · rw [h_unreachable] at hbyte ⊢
    exact step_unreachable p visitor observe hrecords capacity hbyte
  by_cases h_i32_const : opcode = code.OP_I32_CONST
  · rw [h_i32_const] at hbyte ⊢
    exact step_i32_const p visitor observe hrecords capacity hbyte
  by_cases h_i64_const : opcode = code.OP_I64_CONST
  · rw [h_i64_const] at hbyte ⊢
    exact step_i64_const p visitor observe hrecords capacity hbyte
  by_cases h_f32_const : opcode = code.OP_F32_CONST
  · rw [h_f32_const] at hbyte ⊢
    exact step_f32_const p visitor observe hrecords capacity hbyte
  by_cases h_f64_const : opcode = code.OP_F64_CONST
  · rw [h_f64_const] at hbyte ⊢
    exact step_f64_const p visitor observe hrecords capacity hbyte
  by_cases h_drop : opcode = code.OP_DROP
  · rw [h_drop] at hbyte ⊢
    exact step_drop p visitor observe hrecords capacity hbyte
  by_cases h_select : opcode = code.OP_SELECT
  · rw [h_select] at hbyte ⊢
    exact step_select p visitor observe hrecords capacity hbyte
  by_cases h_local_get : opcode = code.OP_LOCAL_GET
  · rw [h_local_get] at hbyte ⊢
    exact step_local_get p visitor observe hrecords capacity hbyte
  by_cases h_local_set : opcode = code.OP_LOCAL_SET
  · rw [h_local_set] at hbyte ⊢
    exact step_local_set p visitor observe hrecords capacity hbyte
  by_cases h_local_tee : opcode = code.OP_LOCAL_TEE
  · rw [h_local_tee] at hbyte ⊢
    exact step_local_tee p visitor observe hrecords capacity hbyte
  by_cases h_global_get : opcode = code.OP_GLOBAL_GET
  · rw [h_global_get] at hbyte ⊢
    exact step_global_get p visitor observe hrecords capacity hbyte
  by_cases h_global_set : opcode = code.OP_GLOBAL_SET
  · rw [h_global_set] at hbyte ⊢
    exact step_global_set p visitor observe hrecords capacity hbyte
  by_cases h_memory_size : opcode = code.OP_MEMORY_SIZE
  · rw [h_memory_size] at hbyte ⊢
    exact step_memory_size p visitor observe hrecords capacity hbyte
  by_cases h_memory_grow : opcode = code.OP_MEMORY_GROW
  · rw [h_memory_grow] at hbyte ⊢
    exact step_memory_grow p visitor observe hrecords capacity hbyte
  have hreserved : (0x06 ≤ opcode.val ∧ opcode.val ≤ 0x0A) ∨
      (0x12 ≤ opcode.val ∧ opcode.val ≤ 0x19) ∨
      (0x1C ≤ opcode.val ∧ opcode.val ≤ 0x1F) ∨
      (0x25 ≤ opcode.val ∧ opcode.val ≤ 0x27) := by
    simp only [controlOpcodes, List.mem_cons, not_or] at hscalar
    simp only [global_simps] at *
    scalar_tac
  intro v result final v' h
  rw [code.step.reserved visitor st.core data env ctx opcode v hreserved] at h
  simp only [Result.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨[], by simp, .silent _ _ (.empty _)⟩

/-- Unary checking preserves a decoded cursor even when the callback rejects. -/
theorem conversion_trace {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (operation : Numeric.Operation) (unary : operation.binary = false)
    (pos : Usize) (action : Action)
    (token : actionToken action [] = some (.plain operation.instruction))
    (not_table : action.opcode ≠ some 14#u8)
    (bytes : At data p.start (.plain operation.instruction) pos)
    (v : V) (result : BodyResult) (final : code.OpIterState) (v' : V)
    (run : CoreVisitor.run
      (code.read_conversion {st.core with pos := pos} operation.input operation.output)
      (fun v s (_ : Unit) => invoke visitor v (.op s action)) v =
        .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => action)
    ?_ v result final v' run
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, vals⟩ := p.opened
  have spec := Numeric.read.segment operation {st.core with pos := pos} outer p.current.vals vals
    (by simp [Control.base, ctrls, base]) capacity
  simp only [Numeric.read, unary, Bool.false_eq_true, ↓reduceIte] at spec
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  exact ⟨_, token, not_table, by simpa only [spec.2.1] using bytes⟩

/-- Scalar extension callbacks retain their complete opcode and prefix bytes. -/
theorem extended_scalar_records {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (v : V) (result : BodyResult) (final : code.OpIterState) (v' : V)
    (run : code.step_extended visitor st.core data env ctx opcode v =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  cases hm : NumericExtensions.signMeaning opcode with
  | some operation =>
    rw [code.step_extended.sign visitor st.core data env ctx opcode operation v hm] at run
    have unary := (NumericExtensions.sign_properties hm).1
    have bytes : At data p.start (.plain operation.instruction) st.core.pos :=
      At.of_immediate p.inbounds hbyte p.pos (.signExtension opcode operation hm)
        (Wasm.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))
    have bounds := (NumericExtensions.sign_properties hm).2.2
    rcases opcode with ⟨⟨n, hn⟩⟩
    change 192 ≤ n ∧ n ≤ 196 at bounds
    obtain ⟨lower, upper⟩ := bounds
    interval_cases n
    all_goals simp [NumericExtensions.signMeaning, UScalar.val] at hm
    all_goals subst operation
    all_goals first
      | exact conversion_trace p visitor observe records capacity _ unary st.core.pos
          (.extendedNumeric .i32_extend8_s) rfl (by decide) bytes v result final v' run
      | exact conversion_trace p visitor observe records capacity _ unary st.core.pos
          (.extendedNumeric .i32_extend16_s) rfl (by decide) bytes v result final v' run
      | exact conversion_trace p visitor observe records capacity _ unary st.core.pos
          (.extendedNumeric .i64_extend8_s) rfl (by decide) bytes v result final v' run
      | exact conversion_trace p visitor observe records capacity _ unary st.core.pos
          (.extendedNumeric .i64_extend16_s) rfl (by decide) bytes v result final v' run
      | exact conversion_trace p visitor observe records capacity _ unary st.core.pos
          (.extendedNumeric .i64_extend32_s) rfl (by decide) bytes v result final v' run
  | none =>
    by_cases hp : opcode = code.OP_MISC_PREFIX
    · have he : opcode = 0xFC#u8 := by simpa [global_simps] using hp
      rw [he] at hbyte run
      rw [code.step_extended.prefixed] at run
      obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
      simp only [prefixedStep, hr, bind_ok] at run
      cases r with
      | Err e =>
        simp only [Result.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨[], by simp, .silent _ _ (.empty _)⟩
      | Ok pair =>
        obtain ⟨subopcode, next⟩ := pair
        cases hs : NumericExtensions.saturatingMeaning subopcode with
        | none =>
          simp only [hs, Result.ok.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          exact ⟨[], by simp, .silent _ _ (.empty _)⟩
        | some operation =>
          simp only [hs] at run
          have unary := NumericExtensions.saturating_unary hs
          have bytes : At data p.start (.plain operation.instruction) next := by
            obtain ⟨bytes, hbytes, length, bound, encoding⟩ := hd
            exact At.of_immediate p.inbounds hbyte p.pos (.saturating subopcode operation hs encoding)
              ⟨hbytes, length, bound⟩
          have bound : subopcode.val < 8 := by
            unfold NumericExtensions.saturatingMeaning at hs
            split at hs <;> simp_all
          rcases subopcode with ⟨⟨n, hn⟩⟩
          change n < 8 at bound
          interval_cases n
          all_goals simp [NumericExtensions.saturatingMeaning, UScalar.val] at hs
          all_goals subst operation
          all_goals first
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i32_trunc_sat_f32_s) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i32_trunc_sat_f32_u) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i32_trunc_sat_f64_s) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i32_trunc_sat_f64_u) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i64_trunc_sat_f32_s) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i64_trunc_sat_f32_u) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i64_trunc_sat_f64_s) rfl (by decide) bytes v result final v' run
            | exact conversion_trace p visitor observe records capacity _ unary next
                (.extendedNumeric .i64_trunc_sat_f64_u) rfl (by decide) bytes v result final v' run
    · rw [code.step_extended.base visitor st.core data env ctx opcode v hm hp] at run
      rw [scalar_context visitor st.core data env ctx ⟨locals, p.ft.results⟩ opcode v hscalar hlocals] at run
      exact base_scalar_records p visitor observe records capacity opcode hscalar hbyte v result final v' run

/-- Core 2.0 delegates inherited scalar and sign-extension bytes unchanged. -/
theorem scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (capacity : st.core.vals.val.length < Usize.max)
    (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hbase : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253])
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    StepRecords p visitor observe ctx opcode := by
  intro v result final v' run
  rw [code.step_wasm2.base visitor st.core data env ctx opcode v hbase] at run
  exact extended_scalar_records p visitor observe records capacity ctx hlocals opcode hscalar hbyte
    v result final v' run

end Itasca.MultiValue.CallbackBytes
