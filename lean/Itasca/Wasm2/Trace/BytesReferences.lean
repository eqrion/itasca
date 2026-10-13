import Itasca.Wasm2.Trace.Bytes

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.CallbackBytes

open VisitorTrace CallbackTrace

theorem ref_null {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 208#u8) :
    StepRecords p visitor observe ctx 208#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_null] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .ref_null ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.REF_NULL (Translate.referenceType a)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_ref_null.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun rt pos => At data p.start (.plain (.REF_NULL (Translate.referenceType rt))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_reference_type.spec st.core data)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  exact ⟨hv, hc, fun rt hok => At.of_immediate p.inbounds byte p.pos
    (.reference (.refNull rt)) (hd rt hok)⟩

theorem typed_select {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8) :
    StepRecords p visitor observe ctx 28#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.typed_select] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .select_typed ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.SELECT (some [Translate.valueType a])), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_typed_select.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun ty pos => At data p.start (.plain (.SELECT (some [Translate.valueType ty]))) pos) ?_ capacity a s hr
  apply WP.spec_mono (selectType.spec st.core data)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro ty hok
  obtain ⟨count, hb, he⟩ := hd ty hok
  exact At.of_immediate p.inbounds byte p.pos (.reference (.selectTyped ty he)) hb

theorem table_get {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 37#u8) :
    StepRecords p visitor observe ctx 37#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.table_get] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .table_get ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.TABLE_GET (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_get.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun idx pos => At data p.start (.plain (.TABLE_GET (.mk_uN idx.val))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_table.spec st.core data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hs, hl, hb, he⟩ := (hd idx ty hok).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.tableGet idx he)) ⟨hs, hl, hb⟩

theorem table_set {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 38#u8) :
    StepRecords p visitor observe ctx 38#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.table_set] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .table_set ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.TABLE_SET (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_set.fixed] at hr
  apply metadata_bytes p _ _ _ _ (fun idx pos => At data p.start (.plain (.TABLE_SET (.mk_uN idx.val))) pos) ?_ capacity a s hr
  apply WP.spec_mono (code.take_table.spec st.core data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hs, hl, hb, he⟩ := (hd idx ty hok).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.tableSet idx he)) ⟨hs, hl, hb⟩

theorem ref_func {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 210#u8) :
    StepRecords p visitor observe ctx 210#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_func] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records .ref_func ?_ v result final v' run
  intro s a hr
  refine ⟨.plain (.REF_FUNC (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  have spec := code.read_ref_func.spec st.core data env capacity
  rw [hr, WP.spec_ok] at spec
  obtain ⟨bytes, hs, hl, hb, he⟩ := (spec.2 a rfl).1
  exact At.of_immediate p.inbounds byte p.pos (.reference (.refFunc a he)) ⟨hs, hl, hb⟩

theorem ref_is_null {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (capacity : st.core.vals.val.length < Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 209#u8) :
    StepRecords p visitor observe ctx 209#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.ref_is_null] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => .ref_is_null) ?_ v result final v' run
  intro s a hr
  refine ⟨.plain .REF_IS_NULL, rfl, by simp [Action.opcode], ?_⟩
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := code.read_ref_is_null.segment st.core outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) capacity
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  exact At.of_immediate p.inbounds byte p.pos (.reference .refIsNull)
    (by simpa [spec.2.1] using Wasm1.BytesAt.nil data st.core.pos (by have := p.pos; have := p.inbounds; omega))

end Itasca.Wasm2.CallbackBytes
