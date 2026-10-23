import Itasca.Wasm2.Trace.BytesReferences

/-!
# Byte provenance for bulk and table callbacks

`ReadBytes` facts for each bulk memory and table reader (`memory_init_bytes`, `table_copy_bytes`,
`table_grow_bytes`, ...), assembled in `bulk` into an exact callback trace for `code.step_bulk`,
including reader rejection and callback rejection.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

theorem memory_init_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem data_drop_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem memory_copy_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem memory_fill_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem table_init_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem elem_drop_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.take_element {st.core with pos := next} data env) (fun (a : U32 × types.ValueType) => .elem_drop a.1) := by
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

theorem table_copy_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem table_grow_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem table_size_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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

theorem table_fill_bytes {data env profile locals index st} (p : Pending data env profile locals index st)
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
theorem bulk {data env profile locals index st} (p : Pending data env profile locals index st)
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
    exact CallbackTrace.run_step_trace data p.start _ visitor observe records (fun (a : U32 × types.ValueType) => .elem_drop a.1)
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
