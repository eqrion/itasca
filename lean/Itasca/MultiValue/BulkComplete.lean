import Itasca.MultiValue.ReferencesComplete

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Completeness

theorem Frame.memory_fill {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (middle next : Usize) (front : List valtype)
    (hprefix : Leb128.Decoded data st.core.pos 11#u32 middle)
    (hb : Wasm.BytesAt data middle [0#u8] next) (hmem : 0 < env.mem_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ [.I32, .I32, .I32])) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hmeta : code.read_bulk_memory {st.core with pos := middle} data env =
      .ok (.Ok (), {st.core with pos := next}) := by
    exact code.read_bulk_memory.complete {st.core with pos := middle} data env next hb hmem
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.read_bulk_memory {st.core with pos := middle} data env)
    () next (fun _ => [.I32, .I32, .I32]) (fun _ => none) id front hmeta hsize
    (by simpa [Simd.inputTypes, Translate.valueType] using hr)
  rw [← code.read_memory_fill.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ (fun v s _ => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_memory_fill v s) () s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 11#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.memory_copy {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (middle next : Usize) (front : List valtype)
    (hprefix : Leb128.Decoded data st.core.pos 10#u32 middle)
    (hb : Wasm.BytesAt data middle [0#u8, 0#u8] next) (hmem : 0 < env.mem_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ [.I32, .I32, .I32])) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hmeta : memoryCopyMetadata {st.core with pos := middle} data env =
      .ok (.Ok (), {st.core with pos := next}) := by
    obtain ⟨reserved, hfirst, hsecond⟩ := (show Wasm.BytesAt data middle ([0#u8] ++ [0#u8]) next from hb).split
    simp [memoryCopyMetadata, code.read_bulk_memory.complete {st.core with pos := middle} data env reserved hfirst hmem,
      code.read_reserved_zero.complete {st.core with pos := reserved} data next hsecond]
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (memoryCopyMetadata {st.core with pos := middle} data env)
    () next (fun _ => [.I32, .I32, .I32]) (fun _ => none) id front hmeta hsize
    (by simpa [Simd.inputTypes, Translate.valueType] using hr)
  rw [← code.read_memory_copy.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ (fun v s _ => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_memory_copy v s) () s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 10#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.memory_init {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index : U32) (middle next : Usize) (front : List valtype)
    (idx count : U32) (dataBytes : List U8)
    (he : Leb128.Encoding dataBytes idx.val) (hcount : env.data_count = some count) (hidx : idx.val < count.val)
    (hprefix : Leb128.Decoded data st.core.pos 8#u32 middle)
    (hb : Wasm.BytesAt data middle (dataBytes ++ [0#u8]) next) (hmem : 0 < env.mem_types.val.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ [.I32, .I32, .I32])) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hmeta : memoryInitMetadata {st.core with pos := middle} data env =
      .ok (.Ok idx, {st.core with pos := next}) := by
    obtain ⟨reserved, hindex, hzero⟩ := hb.split
    simp [memoryInitMetadata, code.take_data_index.complete {st.core with pos := middle} data env idx count reserved
      (hindex.u32_decoded idx he) hcount hidx,
      code.read_bulk_memory.complete {st.core with pos := reserved} data env next hzero hmem]
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (memoryInitMetadata {st.core with pos := middle} data env)
    idx next (fun _ => [.I32, .I32, .I32]) (fun _ => none) id front hmeta hsize
    (by simpa [Simd.inputTypes, Translate.valueType] using hr)
  rw [← code.read_memory_init.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _ (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_memory_init v s a) idx s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 8#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.data_drop {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index idx : U32) (middle next : Usize) (front : List valtype)
    (count : U32) (hcount : env.data_count = some count) (hidx : idx.val < count.val)
    (hprefix : Leb128.Decoded data st.core.pos 9#u32 middle)
    (hd : Leb128.Decoded data middle idx next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands front) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_data_index {st.core with pos := middle} data env)
    idx next (fun _ => []) (fun _ => none) id front
    (code.take_data_index.complete {st.core with pos := middle} data env idx count next hd hcount hidx) hsize (by simpa [Simd.inputTypes] using hr)
  rw [metadataOperands.empty] at hs
  exact f.reader_step data env ctx index 252#u8 _ (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_data_drop v s a) idx s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 9#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.elem_drop {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index idx : U32) (middle next : Usize) (front : List valtype)
    (hidx : idx.val < env.elements.val.length)
    (hprefix : Leb128.Decoded data st.core.pos 13#u32 middle)
    (hd : Leb128.Decoded data middle idx next)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands front) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read (code.take_element {st.core with pos := middle} data env)
    (idx, ModuleConstants.referenceValueType env.elements.val[idx.val].elem) next (fun _ => []) (fun _ => none) id front
    (code.take_element.complete {st.core with pos := middle} data env idx next hd hidx) hsize (by simpa [Simd.inputTypes] using hr)
  rw [metadataOperands.empty] at hs
  exact f.reader_step data env ctx index 252#u8 _ (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_elem_drop v s a.1) (idx, ModuleConstants.referenceValueType env.elements.val[idx.val].elem) s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 13#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.table_init {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index i j : U32) (middle next : Usize) (front : List valtype)
    (firstBytes secondBytes : List U8)
    (hfirst : Leb128.Encoding firstBytes i.val) (hsecond : Leb128.Encoding secondBytes j.val)
    (hprefix : Leb128.Decoded data st.core.pos 12#u32 middle)
    (hb : Wasm.BytesAt data middle (firstBytes ++ secondBytes) next)
    (hi : i.val < env.elements.val.length) (hj : j.val < env.table_types.val.length)
    (helem : env.elements.val[i.val].elem = env.table_types.val[j.val].elem)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ [.I32, .I32, .I32])) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨between, hfirstSpan, hsecondSpan⟩ := hb.split
  have hfirstRead := code.take_element.complete {st.core with pos := middle} data env i between
    (hfirstSpan.u32_decoded i hfirst) hi
  have hsecondRead := code.take_table.complete {st.core with pos := between} data env j next
    (hsecondSpan.u32_decoded j hsecond) hj
  have hmeta : referencePairMetadata (code.take_element {st.core with pos := middle} data env) data env =
      .ok (.Ok (i, j), {st.core with pos := next}) := by
    simp [referencePairMetadata, hfirstRead, hsecondRead, helem]
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read
    (referencePairMetadata (code.take_element {st.core with pos := middle} data env) data env)
    (i, j) next (fun _ => [.I32, .I32, .I32]) (fun _ => none) id front hmeta hsize
    (by simpa [Simd.inputTypes, Translate.valueType] using hr)
  rw [← code.read_table_init.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _
    (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_table_init v s a.1 a.2)
    (i, j) s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 12#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

theorem Frame.table_copy {st} (f : Frame st) (data : Slice U8) (env : module.Env)
    (ctx : code.Context) (index i j : U32) (middle next : Usize) (front : List valtype)
    (firstBytes secondBytes : List U8)
    (hfirst : Leb128.Encoding firstBytes i.val) (hsecond : Leb128.Encoding secondBytes j.val)
    (hprefix : Leb128.Decoded data st.core.pos 14#u32 middle)
    (hb : Wasm.BytesAt data middle (firstBytes ++ secondBytes) next)
    (hi : i.val < env.table_types.val.length) (hj : j.val < env.table_types.val.length)
    (helem : env.table_types.val[i.val].elem = env.table_types.val[j.val].elem)
    (hsize : st.core.vals.val.length < Usize.max)
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ [.I32, .I32, .I32])) :
    ∃ s, step st data env ctx index 252#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output front s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨between, hfirstSpan, hsecondSpan⟩ := hb.split
  have hfirstRead := code.take_table.complete {st.core with pos := middle} data env i between
    (hfirstSpan.u32_decoded i hfirst) hi
  have hsecondRead := code.take_table.complete {st.core with pos := between} data env j next
    (hsecondSpan.u32_decoded j hsecond) hj
  have hmeta : referencePairMetadata (code.take_table {st.core with pos := middle} data env) data env =
      .ok (.Ok (i, j), {st.core with pos := next}) := by
    simp [referencePairMetadata, hfirstRead, hsecondRead, helem]
  obtain ⟨s, hs, hp, hout, hl⟩ := f.metadata_read
    (referencePairMetadata (code.take_table {st.core with pos := middle} data env) data env)
    (i, j) next (fun _ => [.I32, .I32, .I32]) (fun _ => none) id front hmeta hsize
    (by simpa [Simd.inputTypes, Translate.valueType] using hr)
  rw [← code.read_table_copy.fixed] at hs
  exact f.reader_step data env ctx index 252#u8 _
    (fun v s a => code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor.on_table_copy v s a.1 a.2)
    (i, j) s next _ (by decide)
    (by rw [code.step_wasm2.bulk _ _ _ _ _ 14#u32 middle _ hprefix (by decide), code.step_bulk.eq_runs]; rfl)
    hs rfl hp (by simpa [Simd.outputTypes] using hout) hl hsize

end Itasca.MultiValue.Completeness
