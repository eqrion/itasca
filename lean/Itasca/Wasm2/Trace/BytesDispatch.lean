import Itasca.Wasm2.Trace.BytesReferences
import Itasca.Wasm2.Simd.Sound
import Itasca.Wasm2.Trace.BytesScalar

/-!
Sections, each formerly its own module: BytesBulk, BytesSimd, BytesDispatch.
-/

/-! ## BytesBulk -/

section

/-!
# Byte provenance for bulk and table callbacks

`ReadBytes` facts for each bulk memory and table reader (`memory_init_bytes`, `table_copy_bytes`,
`table_grow_bytes`, ...), assembled in `bulk` into an exact callback trace for `code.step_bulk`,
including reader rejection and callback rejection.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

theorem memory_init_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_memory_init {st.core with pos := next} data env) (.memory_init) := by
  intro s a hr
  refine ⟨.plain (.MEMORY_INIT (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_memory_init.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.MEMORY_INIT (.mk_uN a.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (memoryInitMetadata.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro idx hok
  obtain ⟨bytes, hb, he, _⟩ := hd idx hok
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 8#u32 hpe (.memoryInit idx he))
    ((Wasm1.BytesAt.mk hp hpl hpb).append hb)

theorem data_drop_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.take_data_index {st.core with pos := next} data env) (.data_drop) := by
  intro s a hr
  refine ⟨.plain (.DATA_DROP (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [← metadataOperands.empty (code.take_data_index {st.core with pos := next} data env)] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.DATA_DROP (.mk_uN a.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.take_data_index.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro idx hok
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx hok).1
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 9#u32 hpe (.dataDrop idx hencoding))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem memory_copy_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_memory_copy {st.core with pos := next} data env) (fun _ => .memory_copy) := by
  intro s a hr
  refine ⟨.plain (.MEMORY_COPY), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_memory_copy.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.MEMORY_COPY)) pos) ?_ hsize a s hr
  apply WP.spec_mono (memoryCopyMetadata.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro u hok
  cases u
  obtain ⟨hb, _⟩ := hd hok
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 10#u32 hpe .memoryCopy)
    ((Wasm1.BytesAt.mk hp hpl hpb).append hb)

theorem memory_fill_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_memory_fill {st.core with pos := next} data env) (fun _ => .memory_fill) := by
  intro s a hr
  refine ⟨.plain (.MEMORY_FILL), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_memory_fill.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.MEMORY_FILL)) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.read_bulk_memory.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  intro u hok
  cases u
  obtain ⟨hb, _⟩ := hd hok
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 11#u32 hpe .memoryFill)
    ((Wasm1.BytesAt.mk hp hpl hpb).append hb)

theorem table_init_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_init {st.core with pos := next} data env) (fun (a : U32 × U32) => .table_init a.1 a.2) := by
  intro s a hr
  refine ⟨.plain (.TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_init.fixed] at hr
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elements.val.length,
        ty = ModuleConstants.referenceValueType env.elements.val[i.val].elem)
    (code.take_element.spec {st.core with pos := next} data env)
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono hmetadata
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨i, j⟩ hok
  obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
  obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
  obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 12#u32 hpe (.tableInit i j hie hje))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ((Wasm1.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))

theorem elem_drop_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.take_element {st.core with pos := next} data env) (fun (a : U32 × wasm_types.ValueType) => .elem_drop a.1) := by
  intro s a hr
  refine ⟨.plain (.ELEM_DROP (.mk_uN a.1.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [← metadataOperands.empty (code.take_element {st.core with pos := next} data env)] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.ELEM_DROP (.mk_uN a.1.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.take_element.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 13#u32 hpe (.elemDrop idx hencoding))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_copy_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_copy {st.core with pos := next} data env) (fun (a : U32 × U32) => .table_copy a.1 a.2) := by
  intro s a hr
  refine ⟨.plain (.TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_copy.fixed] at hr
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.table_types.val.length,
        ty = ModuleConstants.referenceValueType env.table_types.val[i.val].elem)
    (code.take_table.spec {st.core with pos := next} data env)
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono hmetadata
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  refine ⟨hv, hc, ?_⟩
  rintro ⟨i, j⟩ hok
  obtain ⟨middle, ty, ⟨hdi, _⟩, hdj, _⟩ := hd i j hok
  obtain ⟨ibs, his, hil, hib, hie⟩ := hdi
  obtain ⟨jbs, hjs, hjl, hjb, hje⟩ := hdj
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 14#u32 hpe (.tableCopy i j hie hje))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ((Wasm1.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))

theorem table_grow_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 15#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_grow {st.core with pos := next} data env) (.table_grow) := by
  intro s a hr
  refine ⟨.plain (.TABLE_GROW (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_grow.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.TABLE_GROW (.mk_uN a.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  dsimp only at hv hc hd ⊢
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 15#u32 hpe (.tableGrow idx hencoding))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_size_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 16#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_size {st.core with pos := next} data env) (.table_size) := by
  intro s a hr
  refine ⟨.plain (.TABLE_SIZE (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_size.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.TABLE_SIZE (.mk_uN a.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  dsimp only at hv hc hd ⊢
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 16#u32 hpe (.tableSize idx hencoding))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_fill_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 17#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_fill {st.core with pos := next} data env) (.table_fill) := by
  intro s a hr
  refine ⟨.plain (.TABLE_FILL (.mk_uN a.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_fill.fixed] at hr
  apply metadata_bytes_at p next _ _ _ _ (fun a pos => At data p.start (.plain (.TABLE_FILL (.mk_uN a.val))) pos) ?_ hsize a s hr
  apply WP.spec_mono (code.take_table.spec {st.core with pos := next} data env)
  rintro ⟨res, decoded⟩ ⟨hv, hc, hd⟩
  dsimp only at hv hc hd ⊢
  refine ⟨hv, hc, ?_⟩
  rintro ⟨idx, ty⟩ hok
  obtain ⟨bytes, hbytes, hlen, hbound, hencoding⟩ := (hd idx ty hok).1
  obtain ⟨prefixBytes, hp, hpl, hpb, hpe⟩ := hprefix
  exact At.of_immediate p.inbounds hbyte p.pos (.bulk 17#u32 hpe (.tableFill idx hencoding))
    ((Wasm1.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

/-- Exact bulk dispatch trace includes reader rejection and callback rejection. -/
theorem bulk {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (opcode : U32) (hprefix : Leb128.Decoded data st.core.pos opcode next)
    (hsize : st.core.vals.val.length < Usize.max)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : code.step_bulk visitor {st.core with pos := next} data env opcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [code.step_bulk.eq_runs] at run
  unfold bulkStep at run
  split at run
  case h_1 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (.memory_init)
      (memory_init_bytes p hbyte next hprefix hsize) v result final v' run
  case h_2 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (.data_drop)
      (data_drop_bytes p hbyte next hprefix hsize) v result final v' run
  case h_3 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => .memory_copy)
      (memory_copy_bytes p hbyte next hprefix hsize) v result final v' run
  case h_4 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => .memory_fill)
      (memory_fill_bytes p hbyte next hprefix hsize) v result final v' run
  case h_5 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U32 × U32) => .table_init a.1 a.2)
      (table_init_bytes p hbyte next hprefix hsize) v result final v' run
  case h_6 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U32 × wasm_types.ValueType) => .elem_drop a.1)
      (elem_drop_bytes p hbyte next hprefix hsize) v result final v' run
  case h_7 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U32 × U32) => .table_copy a.1 a.2)
      (table_copy_bytes p hbyte next hprefix hsize) v result final v' run
  case h_8 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (.table_grow)
      (table_grow_bytes p hbyte next hprefix hsize) v result final v' run
  case h_9 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (.table_size)
      (table_size_bytes p hbyte next hprefix hsize) v result final v' run
  case h_10 =>
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (.table_fill)
      (table_fill_bytes p hbyte next hprefix hsize) v result final v' run
  case h_11 =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩

end Itasca.Wasm2.CallbackBytes

end

/-! ## BytesSimd -/

section

/-!
# Byte provenance for SIMD callbacks

Independent byte provenance for each SIMD class dispatched by `code.step_simd` (`simd_pure`,
`simd_lane`, `simd_const`, `simd_shuffle`, `simd_memory`, `simd_memory_lane`), assembled in
`simd` for every ordinary return. `fixed_trace` is the shared case where the operand checker
fails after a decoded immediate.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

/-- The operand checker preserves the cursor even when its operand check fails. -/
theorem fixed_trace {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (action : Action) (token : Token)
    (haction : actionToken action [] = some token) (hbranch : action.opcode ≠ some 0x0E#u8)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max) (hencoded : At data p.start token pos)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : CoreVisitor.run (Simd.readFixed {st.core with pos := pos} inputs output)
      (fun v s _ => invoke visitor v (.op s action)) v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => action) ?_ v result final v' run
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := Simd.readFixed.segment {st.core with pos := pos} inputs output outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) hsize
  rw [hr, WP.spec_ok] at spec
  dsimp only at spec
  exact ⟨token, haction, hbranch, by simpa [spec.2.1] using hencoded⟩

theorem simd_pure {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.Operation)
    (hmap : Simd.pureMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : At data p.start (.plain op.instruction) pos)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.pure _ _ _ _ _ _ _ hmap, Simd.signature_fixed] at run
  exact fixed_trace p visitor observe records (.simd subopcode) (.plain op.instruction)
    (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
    _ _ pos hsize hencoded v result final v' run

theorem simd_lane {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.LaneOperation)
    (hmap : Simd.laneMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ lane next, Wasm1.BytesAt data pos [lane] next →
      At data p.start (.plain (op.instruction (.mk_uN lane.val))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.lane _ _ _ _ _ _ _ hmap, Simd.lane_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hlane⟩ := WP.spec_imp_exists
    (Simd.take_lane_spec {st.core with pos := pos} data op.runtime.2.1)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.laneReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok lane =>
    obtain ⟨_, hbytes⟩ := hlane lane rfl
    rw [hstate, Simd.carryFixed.run] at run
    exact fixed_trace p visitor observe records (.simd_lane subopcode lane)
      (.plain (op.instruction (.mk_uN lane.val)))
      (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
      _ _ decoded.pos hsize (hencoded lane decoded.pos hbytes) v result final v' run

theorem simd_const {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.vectorConstant low high)) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env 12#u32 v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.constant, Simd.const_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists
    (Simd.take_bits_spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.constReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok pair =>
    obtain ⟨low, high⟩ := pair
    rw [hstate, Simd.carryFixed.run] at run
    exact fixed_trace p visitor observe records (.simd_const low high)
      (.plain (Simd.vectorConstant low high)) rfl (by simp [Action.opcode])
      _ _ decoded.pos hsize (hencoded low high decoded.pos (hbits low high rfl)) v result final v' run

theorem simd_shuffle {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (pos : Usize) (hpos : pos.val ≤ data.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.shuffle low high)) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env 13#u32 v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.shuffle] at run
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U64 × U64) => .simd_shuffle a.1 a.2) ?_ v result final v' run
  intro s a hr
  obtain ⟨low, high⟩ := a
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := Simd.shuffle_segment {st.core with pos := pos} data outer p.current.vals stack
    (by simp [Control.base, ctrls, base]) hsize hpos
  rw [hr, WP.spec_ok] at spec
  obtain ⟨_, _, _, hbits, _⟩ := spec low high rfl
  exact ⟨.plain (Simd.shuffle low high), rfl, by simp [Action.opcode], hencoded low high s.pos hbits⟩

theorem simd_memory {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.memory _ _ _ _ _ _ _ hmap hfull, Simd.full_memory_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.fullMemoryReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨res, hcheck, _⟩ := WP.spec_imp_exists
      (code.check_memory_and_alignment.spec env arg op.runtime.1)
    dsimp only at run
    rw [hcheck] at run
    simp only [bind_ok] at run
    cases res with
    | Err e =>
      simp [CoreVisitor.run, bind_ok, Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok u =>
      rw [hstate, Simd.carryFixed.run] at run
      exact fixed_trace p visitor observe records (.simd_memory subopcode arg)
        (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0)))
        (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
        _ _ decoded.pos hsize (hencoded arg middle decoded.pos halign hoffset) v result final v' run

theorem simd_memory_lane {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle ending lane next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset ending → Wasm1.BytesAt data ending [lane] next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.memoryLane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  simp only [Simd.memoryLaneReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [CoreVisitor.run, bind_ok, Std.uncurry,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨⟨res, laned⟩, hd2, hc2, hvals2, hlane⟩ := WP.spec_imp_exists
      (Simd.take_lane_spec decoded data op.runtime.2.2)
    simp only [hd2, bind_ok, Std.uncurry] at run
    cases res with
    | Err e =>
      simp [CoreVisitor.run, bind_ok, Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok lane =>
      obtain ⟨_, hbytes⟩ := hlane lane rfl
      have hstate : laned = {st.core with pos := laned.pos} :=
        Simd.state_of_stacks laned st.core (hvals2.trans hvals) (hc2.trans hc)
      obtain ⟨res, hcheck, _⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg op.runtime.1)
      dsimp only at run
      rw [hcheck] at run
      simp only [bind_ok] at run
      cases res with
      | Err e =>
        simp [CoreVisitor.run, bind_ok, Std.uncurry,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          Result.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
      | Ok u =>
        rw [hstate, Simd.carryFixed.run] at run
        exact fixed_trace p visitor observe records (.simd_memory_lane subopcode arg lane)
          (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val)))
          (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
          _ _ laned.pos hsize (hencoded arg middle decoded.pos lane laned.pos halign hoffset hbytes)
          v result final v' run

/-- Every ordinary SIMD dispatcher return has an exact independent byte trace. -/
theorem simd {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = 0xFD#u8) :
    StepRecords p visitor observe ctx 0xFD#u8 := by
  intro v result final v' run
  rw [code.step_wasm2.simd, code.step_simd.eq_runs] at run
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Simd.prefixStep, hr, bind_ok] at run
  cases r with
  | Err e =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
  | Ok pair =>
    obtain ⟨subopcode, next⟩ := pair
    obtain ⟨prefixBytes, hs, hn, hb, he⟩ := hd
    have hprefix : Wasm1.BytesAt data st.core.pos prefixBytes next := ⟨hs, hn, hb⟩
    have henc : ∀ op bytes ending, Simd.Immediate subopcode op bytes →
        Wasm1.BytesAt data next bytes ending → At data p.start (.plain op) ending := by
      intro op bytes ending hi hbytes
      exact At.of_immediate p.inbounds hbyte p.pos (.simd subopcode he hi) (hprefix.append hbytes)
    by_cases hconstant : subopcode = 12#u32
    · subst subopcode
      apply simd_const p visitor observe records next hsize ?_ v result final v' run
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.constant low high hlo hhi) hspan
    by_cases hshuffle : subopcode = 13#u32
    · subst subopcode
      apply simd_shuffle p visitor observe records next hb hsize ?_ v result final v' run
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.shuffle low high hlo hhi) hspan
    cases hp : Simd.pureMeaning subopcode.val with
    | some op =>
      exact simd_pure p visitor observe records subopcode op hp next hsize
        (henc _ _ _ (.pure subopcode op hp) (Wasm1.BytesAt.nil data next hb)) v result final v' run
    | none =>
      cases hl : Simd.laneMeaning subopcode.val with
      | some op =>
        apply simd_lane p visitor observe records subopcode op hl next hsize ?_ v result final v' run
        intro lane ending hspan
        exact henc _ _ _ (.lane subopcode op lane hl) hspan
      | none =>
        cases hm : Simd.memoryMeaning subopcode.val with
        | some op =>
          by_cases hfull : op.laneCount = 0
          · apply simd_memory p visitor observe records subopcode op hm hfull next hsize ?_ v result final v' run
            intro arg middle ending halign hoffset
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memory subopcode op arg hm hfull ha4 ho4)
              ((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append ⟨ho1, ho2, ho3⟩)
          · apply simd_memory_lane p visitor observe records subopcode op hm hfull next hsize ?_ v result final v' run
            intro arg middle ending lane ending' halign hoffset hspan
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memoryLane subopcode op arg lane hm hfull ha4 ho4)
              (((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append
                ⟨ho1, ho2, ho3⟩).append hspan)
        | none =>
          simp only [Simd.subStep, Simd.pure_table, Simd.lane_table, Simd.memory_table,
            hp, hl, hm, Option.map_none, bind_ok] at run
          split at run
          · exact False.elim (hconstant (by with_unfolding_all rfl))
          · exact False.elim (hshuffle (by with_unfolding_all rfl))
          · simp only [Result.ok.injEq, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl, rfl⟩ := run
            exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩

end Itasca.Wasm2.CallbackBytes

end

/-! ## BytesDispatch -/

section

/-!
# Byte provenance for the Wasm 2.0 dispatcher

`wasm2_dispatch` combines the reference, bulk and SIMD byte traces with a scalar contract for the
remaining opcodes. `wasm2_scalar` discharges that contract, giving an exact independent callback
byte trace for every non-control step of `code.step_wasm2`.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

/-- Assembles `code.step_wasm2` dispatch from a contract for the scalar opcodes; the reference,
bulk and SIMD cases are discharged here. -/
theorem wasm2_dispatch {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (extended : ∀ (op : U8), op.val ∉ controlOpcodes →
      data.val[p.start.val]'p.inbounds = op →
      ∀ v result final v', code.step_extended visitor st.core data env ctx op v =
        .ok (result, final, v') →
        ∃ observations, observe v' = observe v ++ observations ∧
          CallbackTrace.StepTrace data p.start observations result final) :
    StepRecords p visitor observe ctx opcode := by
  by_cases h253 : opcode = 253#u8
  · rw [h253] at hbyte ⊢
    exact simd p visitor observe records ctx hsize hbyte
  by_cases h28 : opcode = 28#u8
  · rw [h28] at hbyte ⊢
    exact typed_select p visitor observe records ctx hsize hbyte
  by_cases h37 : opcode = 37#u8
  · rw [h37] at hbyte ⊢
    exact table_get p visitor observe records ctx hsize hbyte
  by_cases h38 : opcode = 38#u8
  · rw [h38] at hbyte ⊢
    exact table_set p visitor observe records ctx hsize hbyte
  by_cases h208 : opcode = 208#u8
  · rw [h208] at hbyte ⊢
    exact ref_null p visitor observe records ctx hsize hbyte
  by_cases h209 : opcode = 209#u8
  · rw [h209] at hbyte ⊢
    exact ref_is_null p visitor observe records ctx hsize hbyte
  by_cases h210 : opcode = 210#u8
  · rw [h210] at hbyte ⊢
    exact ref_func p visitor observe records ctx hsize hbyte
  by_cases h252 : opcode = 252#u8
  · rw [h252] at hbyte ⊢
    intro v result final v' run
    rw [code.step_wasm2.prefixed] at run
    obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
    simp only [wasm2PrefixedStep, hr, bind_ok] at run
    cases r with
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok pair =>
      obtain ⟨subopcode, next⟩ := pair
      dsimp only at hd run
      split at run
      · exact extended 252#u8 (by decide) hbyte v result final v' run
      · exact bulk p visitor observe records hbyte next subopcode hd hsize v result final v' run
  have hbase : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28, neq h37, neq h38, neq h208, neq h209, neq h210, neq h252, neq h253⟩
  intro v result final v' run
  rw [code.step_wasm2.base visitor st.core data env ctx opcode v hbase] at run
  exact extended opcode hscalar hbyte v result final v' run

/-- Every non-control Wasm 2.0 step has an exact independent callback byte trace,
including ordinary reader failure and rejecting callbacks. -/
theorem wasm2_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    StepRecords p visitor observe ctx opcode := by
  exact wasm2_dispatch p visitor observe records ctx opcode hscalar hsize hbyte
    (fun op hs hb => extended_scalar_records p visitor observe records hsize ctx hlocals op hs hb)

end Itasca.Wasm2.CallbackBytes

end
