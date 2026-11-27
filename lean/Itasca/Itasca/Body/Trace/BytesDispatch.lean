import Itasca.Body.Trace.Refinement
import Itasca.Body.Simd.Sound
import Itasca.Body.Trace.BytesScalar
import Itasca.Body.Trace.ControlRecords
import Itasca.Module.Definitions
import Itasca.Results.Definitions.Validation
import Itasca.Body.Visitor.ReachedTableLoop

open WebAssembly

/-!
Proofs for Body / Trace.

This module collects BytesDispatch, TableBytes, Acceptance.
Each section documents its contracts and consumers.
-/

/-! ## BytesDispatch -/

section

/-!
# Bytes Dispatch

Bulk and SIMD callback traces retain their exact independent byte meanings. Dispatch composition joins the instruction-family cases into the complete trace relation.
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
namespace Itasca.Body.CallbackBytes
open Visitor.Trace CallbackTrace

theorem memory_init_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 8#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)

theorem data_drop_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 9#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem memory_copy_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 10#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)

theorem memory_fill_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 11#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append hb)

theorem table_init_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 12#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_init {st.core with pos := next} data env) (fun (a : U32 × U32) => .table_init a.1 a.2) := by
  intro s a hr
  refine ⟨.plain (.TABLE_INIT (.mk_uN a.2.val) (.mk_uN a.1.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_init.fixed] at hr
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_element {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.elem_segment_types.val.length,
        ty = Module.Constants.referenceValueType env.elem_segment_types.val[i.val])
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))

theorem elem_drop_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 13#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_copy_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 14#u32 next)
    (hsize : st.core.vals.val.length < Usize.max) :
    ReadBytes data p.start (code.read_table_copy {st.core with pos := next} data env) (fun (a : U32 × U32) => .table_copy a.1 a.2) := by
  intro s a hr
  refine ⟨.plain (.TABLE_COPY (.mk_uN a.1.val) (.mk_uN a.2.val)), rfl, by simp [Action.opcode], ?_⟩
  rw [code.read_table_copy.fixed] at hr
  have hmetadata := referencePairMetadata.spec {st.core with pos := next} data env
    (code.take_table {st.core with pos := next} data env)
    (fun i ty pos => Binary.Leb128.Decoded data next i pos ∧
      ∃ hi : i.val < env.tables.val.length,
        ty = Module.Constants.referenceValueType env.tables.val[i.val].ty.elem)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ((Body.Scalar.BytesAt.mk his hil hib).append ⟨hjs, hjl, hjb⟩))

theorem table_grow_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 15#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_size_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 16#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

theorem table_fill_bytes {data env locals index st} (p : Pending data env locals index st)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (hprefix : Binary.Leb128.Decoded data st.core.pos 17#u32 next)
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
    ((Body.Scalar.BytesAt.mk hp hpl hpb).append ⟨hbytes, hlen, hbound⟩)

/-- Exact bulk dispatch trace includes reader rejection and callback rejection. -/
theorem bulk {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe)
    (hbyte : data.val[p.start.val]'p.inbounds = 252#u8) (next : Usize)
    (opcode : U32) (hprefix : Binary.Leb128.Decoded data st.core.pos opcode next)
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

end Itasca.Body.CallbackBytes

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
namespace Itasca.Body.CallbackBytes
open Visitor.Trace CallbackTrace

/-- The operand checker preserves the cursor even when its operand check fails. -/
theorem fixed_trace {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (action : Action) (token : Token)
    (haction : actionToken action [] = some token) (hbranch : action.opcode ≠ some 0x0E#u8)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max) (hencoded : At data p.start token pos)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Visitor.Core.run (Simd.readFixed {st.core with pos := pos} inputs output)
      (fun v s _ => invoke visitor v (.op s action)) v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  apply CallbackTrace.run_step_trace data p.start _ visitor observe records (fun _ => action) ?_ v result final v' run
  intro s a hr
  obtain ⟨_, outer, _, _, base, _, ctrls, _, stack⟩ := p.opened
  have spec := Simd.readFixed.segment {st.core with pos := pos} inputs output outer p.current.vals stack
    (by simp [Body.Control.base, ctrls, base]) hsize
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
    (by simp [actionToken, Action.token, Simd.pureInstruction_eq, hmap]) (by simp [Action.opcode])
    _ _ pos hsize hencoded v result final v' run

theorem simd_lane {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.LaneOperation)
    (hmap : Simd.laneMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ lane next, Body.Scalar.BytesAt data pos [lane] next →
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
    simp [Visitor.Core.run, bind_ok, Std.uncurry,
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
    simp [Visitor.Core.run, bind_ok, Std.uncurry,
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
    (by simp [Body.Control.base, ctrls, base]) hsize hpos
  rw [hr, WP.spec_ok] at spec
  obtain ⟨_, _, _, hbits, _⟩ := spec low high rfl
  exact ⟨.plain (Simd.shuffle low high), rfl, by simp [Action.opcode], hencoded low high s.pos hbits⟩

theorem simd_memory {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle next, Binary.Leb128.Decoded data pos arg.align middle →
      Binary.Leb128.Decoded data middle arg.offset next →
      At data p.start (.plain (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN 0))) next)
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
    simp [Visitor.Core.run, bind_ok, Std.uncurry,
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
      simp [Visitor.Core.run, bind_ok, Std.uncurry,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok u =>
      rw [hstate, Simd.carryFixed.run] at run
      exact fixed_trace p visitor observe records (.simd_memory subopcode arg)
        (.plain (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN 0)))
        (by simp [actionToken, Action.token, hmap]) (by simp [Action.opcode])
        _ _ decoded.pos hsize (hencoded arg middle decoded.pos halign hoffset) v result final v' run

theorem simd_memory_lane {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle ending lane next, Binary.Leb128.Decoded data pos arg.align middle →
      Binary.Leb128.Decoded data middle arg.offset ending → Body.Scalar.BytesAt data ending [lane] next →
      At data p.start (.plain (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val))) next)
    (v : V) (result : core.result.Result Unit error.OpError) (final : code.OpIterState) (v' : V)
    (run : Simd.subStep visitor {st.core with pos := pos} data env subopcode v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      CallbackTrace.StepTrace data p.start observations result final := by
  rw [Simd.subStep.memory_lane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed] at run
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  simp only [Simd.memoryLaneReader, hd, bind_ok, Std.uncurry] at run
  cases res with
  | Err e =>
    simp [Visitor.Core.run, bind_ok, Std.uncurry,
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
      simp [Visitor.Core.run, bind_ok, Std.uncurry,
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
        simp [Visitor.Core.run, bind_ok, Std.uncurry,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          Result.ok.injEq, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
      | Ok u =>
        rw [hstate, Simd.carryFixed.run] at run
        exact fixed_trace p visitor observe records (.simd_memory_lane subopcode arg lane)
          (.plain (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val)))
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
    have hprefix : Body.Scalar.BytesAt data st.core.pos prefixBytes next := ⟨hs, hn, hb⟩
    have henc : ∀ op bytes ending, Simd.Immediate subopcode op bytes →
        Body.Scalar.BytesAt data next bytes ending → At data p.start (.plain op) ending := by
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
        (henc _ _ _ (.pure subopcode op.instruction (by rw [Simd.pureInstruction_eq, hp]; rfl)) (Body.Scalar.BytesAt.nil data next hb)) v result final v' run
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
              ((show Body.Scalar.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append ⟨ho1, ho2, ho3⟩)
          · apply simd_memory_lane p visitor observe records subopcode op hm hfull next hsize ?_ v result final v' run
            intro arg middle ending lane ending' halign hoffset hspan
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memoryLane subopcode op arg lane hm hfull ha4 ho4)
              (((show Body.Scalar.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append
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

end Itasca.Body.CallbackBytes

end

/-! ## BytesDispatch -/

section

/-!
# Byte provenance for the Wasm 2.0 dispatcher

`instruction_dispatch` combines the reference, bulk and SIMD byte traces with a scalar contract for the
remaining opcodes. `non_control` discharges that contract, giving an exact independent callback
byte trace for every non-control step of `code.step_wasm2`.
-/

open Aeneas Aeneas.Std
namespace Itasca.Body.CallbackBytes
open Visitor.Trace CallbackTrace

/-- Assembles `code.step_wasm2` dispatch from a contract for the scalar opcodes; the reference,
bulk and SIMD cases are discharged here. -/
theorem instruction_dispatch {data env locals index st} (p : Pending data env locals index st)
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
    simp only [miscellaneousStep, hr, bind_ok] at run
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
theorem non_control {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    StepRecords p visitor observe ctx opcode := by
  exact instruction_dispatch p visitor observe records ctx opcode hscalar hsize hbyte
    (fun op hs hb => extended_scalar_records p visitor observe records hsize ctx hlocals op hs hb)

end Itasca.Body.CallbackBytes

end

end

/-! ## TableBytes -/

section

/-!
# Callback byte provenance for `br_table`

`TableSuffix` describes the callbacks of the remaining targets of a branch table, and
`table_loop_records` shows that the extracted `code.branch_table_with_loop` produces one for every
ordinary return. `table_records` adds the count and default target, and `step_br_table` gives the
`StepRecords` for opcode `0x0e`.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Itasca.Body.CallbackTrace

open Visitor.Trace Visitor

/-- A table suffix records only vector labels until the final table callback.
The default target is decoded separately and never emits a label callback. -/
inductive TableSuffix (data : Slice U8) (start : Usize) (remaining : Nat) :
    List Observation → BodyResult → code.OpIterState → Prop where
  | failed {labels depths last final} (e : error.OpError) :
      LabelsAt data start labels depths last → depths.length ≤ remaining →
      Outcomes labels (.Err e) → TableSuffix data start remaining labels (.Err e) final
  | complete {labels depths last fallback final bt reply} :
      LabelsAt data start labels depths last → depths.length = remaining →
      Binary.Leb128.Decoded data last fallback final.pos → AllAccepted labels →
      TableSuffix data start remaining
        (labels ++ [⟨.op final (.br_table fallback bt), reply⟩]) (hookResult reply) final

theorem TableSuffix.prepend {data start middle depth remaining observations result final}
    (decoded : Binary.Leb128.Decoded data start depth middle.pos)
    (trace : TableSuffix data middle.pos remaining observations result final) :
    TableSuffix data start (remaining + 1)
      (⟨.op middle (.br_table_label depth), .Ok ()⟩ :: observations) result final := by
  cases trace with
  | failed e labels count outcomes =>
    exact .failed e (.cons decoded labels) (by simpa using Nat.add_le_add_right count 1)
      (by simpa using outcomes.prepend (before := [⟨.op middle (.br_table_label depth), .Ok ()⟩]) (by simp [AllAccepted]))
  | complete labels count fallback outcomes =>
    simpa using TableSuffix.complete (.cons (reply := .Ok ()) decoded labels)
      (by simpa using count) fallback (by simpa [AllAccepted] using outcomes)

set_option maxHeartbeats 1500000 in
/-- Ordinary returns of the `br_table` target loop record the bytes of every observed label,
including a rejecting label or a label preceding a suffix error. -/
theorem table_loop_records {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (st : code.BodyState) (data : Slice U8) (env : metadata.CodeMetadata)
    (hs : Body.Control.Shape st.core) (ha : st.blocks.val.length = st.core.ctrls.val.length)
    (count i : U32) (arity : Option Usize) (hi : i.val ≤ count.val)
    (v : V) (result : BodyResult) (final : code.BodyState) (v' : V)
    (run : code.branch_table_with_loop visitor st.core data env v count arity i =
      .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      TableSuffix data st.core.pos (count.val - i.val) observations result final.core := by
  generalize hn : count.val - i.val = n
  induction n using Nat.strong_induction_on generalizing st i arity v with
  | h n ih =>
    unfold code.branch_table_with_loop at run
    rw [loop] at run
    simp only [Visitor.table_body_eq visitor data env count st v arity i] at run
    obtain ⟨cf, hb, ht⟩ := Computation.bind_ok_inv _ _ _ run
    unfold Visitor.tableBody at hb
    obtain ⟨⟨r, s⟩, hr, hv, hc, hbytes⟩ := WP.spec_imp_exists (code.read_label_info.bytes st data ha)
    rw [hr] at hb
    cases r with
    | Err e =>
      simp only [bind_ok, Std.uncurry, ok.injEq] at hb
      subst cf
      simp only [ok.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      exact ⟨[], by simp, .failed e (.nil _) (by simp) (.empty _)⟩
    | Ok pair =>
      obtain ⟨depth, ts⟩ := pair
      dsimp only at hv hc
      have hd := hbytes depth ts rfl
      have hs' : Body.Control.Shape s.core :=
        ⟨by simpa [hc] using hs.ordered, by simpa [hc, hv] using hs.bounded⟩
      have ha' : s.blocks.val.length = s.core.ctrls.val.length := by simp [code.BodyState.blocks]
      simp only [bind_ok, Std.uncurry] at hb
      by_cases he : i = count
      · simp only [he, bne_self_eq_false, Bool.false_eq_true, if_false] at hb
        unfold tableRest at hb
        obtain ⟨r, hcheck, hb⟩ := Computation.bind_ok_inv _ _ _ hb
        cases r with
        | Err e =>
          simp only [ok.injEq] at hb
          subst cf
          simp only [ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl, rfl⟩ := ht
          exact ⟨[], by simp, .failed e (.nil _) (by simp) (.empty _)⟩
        | Ok nextArity =>
          simp only [↓reduceIte] at hb
          obtain ⟨ois, ho, hb⟩ := Computation.bind_ok_inv _ _ _ hb
          have spec := code.mark_unreachable_total s.core hs'
          rw [ho, WP.spec_ok] at spec
          have hp : ois.pos = s.core.pos := spec.2.2.1
          obtain ⟨⟨reply, w⟩, hh, hb⟩ := Computation.bind_ok_inv _ _ _ hb
          have hlog := records v (.op ois (.br_table depth ts)) reply w hh
          cases reply <;> simp [code.visit, Std.uncurry] at hb
          all_goals subst cf
          all_goals simp only [ok.injEq, Prod.mk.injEq] at ht
          all_goals obtain ⟨rfl, rfl, rfl⟩ := ht
          all_goals refine ⟨_, hlog, ?_⟩
          all_goals apply TableSuffix.complete (labels := []) (depths := []) (last := st.core.pos) (.nil _)
          all_goals solve | simp [← hn, he] | simpa [hp] using hd | simp [AllAccepted]
      · simp only [bne_iff_ne, if_pos he] at hb
        obtain ⟨⟨reply, w⟩, hh, hb⟩ := Computation.bind_ok_inv _ _ _ hb
        have hlog := records v (.op s.core (.br_table_label depth)) reply w hh
        have hlt : i.val < count.val := by
          have hne : i.val ≠ count.val := fun eq => he (UScalar.eq_of_val_eq eq)
          omega
        cases reply with
        | Err e =>
          simp [code.visit, Std.uncurry] at hb
          subst cf
          simp only [ok.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl, rfl⟩ := ht
          exact ⟨_, hlog, .failed (.Visitor e) (.cons hd (.nil _))
            (by simp; omega) (.single _ (.Err e))⟩
        | Ok u =>
          cases u
          simp only [code.visit, bind_ok, Std.uncurry] at hb
          unfold tableRest at hb
          obtain ⟨r, hcheck, hb⟩ := Computation.bind_ok_inv _ _ _ hb
          cases r with
          | Err e =>
            simp only [ok.injEq] at hb
            subst cf
            simp only [ok.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl, rfl⟩ := ht
            exact ⟨_, hlog, .failed e (.cons hd (.nil _)) (by simp; omega)
              (.of_accepted (by simp [AllAccepted]) _)⟩
          | Ok nextArity =>
            simp only [he, if_false] at hb
            obtain ⟨j, hj, hjv⟩ := WP.spec_imp_exists
              (UScalar.add_spec (x := i) (y := 1#u32) (by scalar_tac))
            simp only [hj, bind_ok, ok.injEq] at hb
            subst cf
            have hrec : code.branch_table_with_loop visitor s.core data env w count
                nextArity j = .ok (result, final, v') := ht
            obtain ⟨observations, hobs, htrace⟩ := ih (count.val - j.val) (by scalar_tac)
              s hs' ha' j nextArity (by scalar_tac) w hrec rfl
            refine ⟨⟨.op s.core (.br_table_label depth), .Ok ()⟩ :: observations, ?_, ?_⟩
            · simpa [List.append_assoc] using hobs.trans (congrArg (· ++ observations) hlog)
            · have hn' : count.val - j.val + 1 = n := by scalar_tac
              simpa [hn'] using htrace.prepend hd

end Itasca.Body.CallbackTrace

namespace Itasca.Body.CallbackTrace

open Visitor.Trace

theorem labels_decoded {data pos observations depths last}
    (h : LabelsAt data pos observations depths last) :
    Body.BrTable.LabelsDecoded data pos depths last := by
  induction h with
  | nil => exact .nil
  | cons hd _ ih => exact (Body.BrTable.LabelsDecoded.snoc .nil hd).append ih

/-- Table decoding includes its count, every observed vector label, and the
separately decoded default. Operand failures before the loop emit no callbacks. -/
theorem table_records {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe)
    (byte : data.val[p.start.val]'p.inbounds = 0x0e#u8)
    (v : V) (result : BodyResult) (final : code.BodyState) (v' : V)
    (run : code.branch_table_with visitor st data env v = .ok (result, final, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      StepTrace data p.start observations result final.core := by
  unfold code.branch_table_with at run
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  rw [hr] at run
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent e st.core (.empty _)⟩
  | Ok pair =>
    obtain ⟨count, first⟩ := pair
    have hcount : Binary.Leb128.Decoded data st.core.pos count first := hd
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.uncurry] at run
    have shape : Body.Control.Shape {st.core with pos := first} :=
      ⟨p.opened.shape.core.ordered, p.opened.shape.core.bounded⟩
    obtain ⟨⟨r, s⟩, hr, hs, hc, hp, _⟩ := WP.spec_imp_exists
      (code.pop_with_type.total {st.core with pos := first} .I32 shape)
    rw [hr] at run
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent e s (.empty _)⟩
    | Ok value =>
      simp only [bind_ok, Std.uncurry] at run
      obtain ⟨observations, log, trace⟩ := table_loop_records visitor observe records
        ⟨s⟩ data env hs (by simp) count 0#u32 none (by simp) v result final v' run
      have hop : Body.Scalar.BytesAt data p.start [0x0E#u8] st.core.pos :=
        .byte data p.start st.core.pos 0x0E#u8 p.inbounds byte p.pos
      have hpos : s.pos = first := hp
      simp only [hpos] at trace
      change TableSuffix data first count.val observations result final.core at trace
      refine ⟨observations, log, ?_⟩
      cases trace with
      | failed e labels len outcomes =>
        exact .unfinished e ⟨st.core.pos, count, first, _, _, hop, hcount, labels, len⟩ outcomes
      | complete labels len fallback outcomes =>
        refine .complete (.table hop hcount labels len fallback ?_) ?_
        · exact At.plain (Body.Scalar.At.of_br_table count _ _ p.inbounds byte p.pos hcount len
            (labels_decoded labels) fallback)
        · exact (Outcomes.single _ _).prepend outcomes

/-- The table arm of the instruction dispatcher returns its handler's exact result. -/
theorem dispatch_br_table {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32) (v : V) :
    code.step_body visitor st data env ctx index 0x0e#u8 v =
      code.branch_table_with visitor st data env v := by
  simp [code.step_body, global_simps,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  conv => rhs; rw [← Std.bind_pure (code.branch_table_with visitor st data env v)]
  congr 1
  funext pair
  obtain ⟨r, s, w⟩ := pair
  cases r <;> simp

end Itasca.Body.CallbackTrace

namespace Itasca.Body.CallbackTrace

open Visitor.Trace

theorem step_br_table {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 0x0e#u8) :
    StepRecords p visitor observe ctx 0x0e#u8 := by
  intro v result final v' run
  rw [dispatch_br_table] at run
  exact table_records p visitor observe records byte v result final v' run

end Itasca.Body.CallbackTrace

end

/-! ## Acceptance -/

section

/-! ## Step -/

section

/-!
# Step-level callback byte provenance

`steps` shows that the extracted `code.step_body` satisfies `StepContract`: every
ordinary return has an exact independent callback byte trace, without a total-visitor premise.
`step_contract_of_table` assembles the scalar, control and non-control leaf traces once the
`br_table` case is supplied.
-/

open Aeneas Aeneas.Std
namespace Itasca.Body.CallbackTrace
open Visitor.Trace

/-- Factors the capacity-guarded scalar arm of `code.step_body` without changing error
outcomes. -/
theorem dispatch_scalar {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32) (opcode : U8) (v : V)
    (hscalar : opcode.val ∉ controlOpcodes) :
    code.step_body visitor st data env ctx index opcode v =
      if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, v)
      else (do
        let (r, s, v') ← code.step_wasm2 visitor st.core data env ctx opcode v
        .ok (r, {st with core := s}, v')) := by
  unfold code.step_body
  split
  case h_1 | h_2 | h_3 | h_4 | h_5 | h_6 | h_7 | h_8 | h_9 | h_10 | h_11 =>
    exact False.elim (hscalar (by decide))
  case h_12 =>
    dsimp only
    split
    · rfl
    · congr 1
      funext pair
      obtain ⟨r, s, v'⟩ := pair
      cases r <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem step_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (byte : data.val[p.start.val]'p.inbounds = opcode) :
    StepRecords p visitor observe ctx opcode := by
  intro v result final v' run
  rw [dispatch_scalar _ _ _ _ _ _ _ _ hscalar] at run
  split at run
  · simp only [Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact ⟨[], by simp, .silent _ _ (.empty _)⟩
  · rename_i capacity
    have size : st.core.vals.val.length < Usize.max := by scalar_tac
    obtain ⟨⟨r, s, w⟩, hr, tail⟩ := Computation.bind_ok_inv _ _ _ run
    simp only [Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact CallbackBytes.non_control p visitor observe records ctx hlocals opcode hscalar size byte
      v r s w hr

/-- Assemble every concrete step once the branch-table protocol is supplied. -/
theorem step_contract_of_table {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals)
    (table : ∀ st (p : Pending data env locals index st),
      data.val[p.start.val]'p.inbounds = 0x0e#u8 →
      StepRecords p visitor observe ctx 0x0e#u8) :
    StepContract visitor observe data env locals ctx index := by
  intro st p v result out v' run
  let opcode := data.val[p.start.val]'p.inbounds
  have byte : data.val[p.start.val]'p.inbounds = opcode := rfl
  change code.step_body visitor st data env ctx index opcode v = _ at run
  by_cases hs : opcode.val ∉ controlOpcodes
  · exact step_scalar p visitor observe records ctx hlocals opcode hs byte v result out v' run
  · have hm := Classical.not_not.mp hs
    obtain ⟨⟨n, hn⟩⟩ := opcode
    change n ∈ controlOpcodes at hm
    simp only [controlOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h <;> subst n
    · exact step_block p visitor observe records ctx byte v result out v' run
    · exact step_loop p visitor observe records ctx byte v result out v' run
    · exact step_if p visitor observe records ctx byte v result out v' run
    · exact step_else p visitor observe records ctx byte v result out v' run
    · exact step_end p visitor observe records ctx byte v result out v' run
    · exact step_br p visitor observe records ctx byte v result out v' run
    · exact step_br_if p visitor observe records ctx byte v result out v' run
    · exact table st p byte v result out v' run
    · exact step_return p visitor observe records ctx byte v result out v' run
    · exact step_call p visitor observe records ctx byte v result out v' run
    · exact step_call_indirect p visitor observe records ctx byte v result out v' run

/-- The full extracted Wasm 2.0 dispatcher satisfies independent callback byte
provenance for every ordinary return, without a total-visitor premise. -/
theorem steps {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata)
    (locals : alloc.vec.Vec wasm_types.ValueType)
    (ctx : code.Context) (index : U32) (hlocals : ctx.locals = locals) :
    StepContract visitor observe data env locals ctx index := by
  exact step_contract_of_table visitor observe records data env locals ctx index hlocals
    (fun _ p byte => step_br_table p visitor observe records ctx byte)

end Itasca.Body.CallbackTrace

end

/-! ## Correspondence -/

section

/-!
# Callback traces of body validation

Trace results for `code.validate_body_with`. `body_trace` gives exact byte provenance for
every ordinary return, `body_trace_sound` shows that accepted callbacks spell an independently
encoded, SpecTec-typed body (`AcceptedBody`), and `body_trace_complete` shows that every such body
forces the complete callback sequence. `instrument_body_trace` and `recorder_body_total` show that
instrumenting a visitor or running the recorder yields these traces without changing the
validation result. `Itasca/Results/Trace` states them as public results.
-/

open Aeneas Aeneas.Std

namespace Itasca

open Visitor.Trace

/-- Every ordinary body return has exact callback byte provenance. A rejected final table may be
partial; an observed rejecting callback is the last one recorded. No valid-input or total-callback
premise is needed. -/
theorem Body.CallbackTrace.body_trace {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (index : U32)
     (v v' : V) (result : BodyResult)
    (run : code.validate_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Body.CallbackTrace.BodyTrace data 0#usize observations result :=
  code.validate_body_with.trace_of_contract visitor observe data env ctx index
    (Body.CallbackTrace.steps visitor observe records data env ctx.locals ctx index rfl)
    v v' result run

/-- Accepted callback syntax and generated typing refer to the same body, by uniqueness of the
independent byte grammar. -/
theorem Body.CallbackTrace.body_trace_sound {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (index : U32)
     (v v' : V)
    (run : code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v')) :
    ∃ observations, observe v' = observe v ++ observations ∧
      Body.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨observations, log, trace⟩ := Body.CallbackTrace.body_trace
    visitor observe records data env ctx index v v' (.Ok ()) run
  obtain ⟨accepted, tokens, next, chunks, endpos⟩ := trace.accepted
  obtain ⟨ft, ops, entry, ⟨tokens', next', bytes, endpos', hsyntax⟩, typed, declared⟩ :=
    code.validate_body_with.sound visitor data env ctx index v v' run
  have equal_pos : next' = next := UScalar.eq_of_val_eq (endpos'.trans endpos.symm)
  subst next'
  have equal_tokens := chunks.encoded.unique bytes
  subst tokens'
  exact ⟨observations, log, accepted, ft, tokens, ops, next, entry, chunks,
    endpos, hsyntax, typed, declared⟩

/-- Independently encoded and typed bodies force a complete callback trace for accepting
recording visitors within the documented resource bounds. -/
theorem Body.CallbackTrace.body_trace_complete {V : Type} (visitor : code.OpVisitor V)
    (observe : V → List Observation) (records : Records visitor observe)
    (accepts : Visitor.Accepts visitor) (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32)
    (environment : CodeEntry.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Body.Validated data env ctx.locals index) (v : V) :
    ∃ v' observations,
      code.validate_body_with visitor data env ctx index v = .ok (.Ok (), v') ∧
      observe v' = observe v ++ observations ∧
      Body.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨v', run⟩ := code.validate_body_with.complete visitor accepts
    data env ctx index environment size body v
  obtain ⟨observations, log, trace⟩ := Body.CallbackTrace.body_trace_sound
    visitor observe records data env ctx index v v' run
  exact ⟨v', observations, run, log, trace⟩

/-- Instrumenting an ordinary execution does not change its result or underlying visitor state.
The added observations satisfy byte provenance. -/
theorem Body.CallbackTrace.instrument_body_trace {V : Type} (visitor : code.OpVisitor V)
    (data : Slice U8) (env : metadata.CodeMetadata) (ctx : code.Context) (index : U32)
     (v : V)
    (log : List Observation) (result : BodyResult) (v' : V)
    (run : code.validate_body_with visitor data env ctx index v = .ok (result, v')) :
    ∃ added,
      code.validate_body_with (instrument visitor) data env ctx index (v, log) =
        .ok (result, (v', log ++ added)) ∧
      Body.CallbackTrace.BodyTrace data 0#usize added result := by
  obtain ⟨added, instrumented⟩ := code.validate_body_with.instrument_forward
    visitor data env ctx index v log result v' run
  obtain ⟨observations, equal_log, trace⟩ := Body.CallbackTrace.body_trace
    (instrument visitor) Prod.snd (instrument_records visitor) data env ctx index
    (v, log) (v', log ++ added) result instrumented
  have equal : added = observations := List.append_cancel_left equal_log
  exact ⟨added, instrumented, equal ▸ trace⟩

/-- The concrete recorder returns a byte-provenance trace on arbitrary input, including malformed
instructions and reserved opcodes. -/
theorem Body.CallbackTrace.recorder_body_total (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32) : ∃ result observations,
    code.validate_body_with recorder data env ctx index [] =
      .ok (result, observations) ∧
      Body.CallbackTrace.BodyTrace data 0#usize observations result := by
  obtain ⟨⟨result, observations⟩, run⟩ := code.validate_body_with.total
    recorder Visitor.Trace.recorder_total data env ctx index []
  obtain ⟨added, equal_log, trace⟩ := Body.CallbackTrace.body_trace
    recorder id recorder_records data env ctx index [] observations result run
  simp only [id_eq, List.nil_append] at equal_log
  exact ⟨result, observations, run, equal_log ▸ trace⟩

end Itasca

end

/-! ## Acceptance -/

section

namespace Itasca.Body.CallbackTrace
open Aeneas Aeneas.Std Visitor.Trace

/-- The concrete `recorder` visitor accepts an independently encoded, typed body and visits every
instruction, with all entries of every branch table in order. -/
theorem Body.CallbackTrace.recorder_body_complete (data : Slice U8) (env : metadata.CodeMetadata)
    (ctx : code.Context) (index : U32)
    (environment : CodeEntry.EnvironmentWithinLimits env)
    (size : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (body : Body.Validated data env ctx.locals index) : ∃ observations,
    code.validate_body_with recorder data env ctx index [] =
      .ok (.Ok (), observations) ∧
      Body.CallbackTrace.AcceptedBody data env ctx index observations := by
  obtain ⟨observations, added, run, equal, trace⟩ :=
    Body.CallbackTrace.body_trace_complete recorder id recorder_records recorder_accepts data env
      ctx index environment size body []
  simp only [id_eq, List.nil_append] at equal
  exact ⟨observations, run, equal ▸ trace⟩


end Itasca.Body.CallbackTrace

end

end
