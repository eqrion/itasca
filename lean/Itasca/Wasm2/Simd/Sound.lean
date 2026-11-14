import Itasca.Wasm2.Simd.Visitor
import Itasca.Handler.RawControl
import Itasca.Wasm2.Simd.LaneReaders
import Itasca.Binary.Wasm2.SyntaxUnique
import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Complete.Frame
import Itasca.Wasm2.Scalar.IndexReader
import Itasca.Wasm2.LoopDispatch

/-!
Sections, each formerly its own module: Complete, Reader, Sound.
-/

/-! ## Complete -/

section

/-!
# Completeness of SIMD instructions

For each SIMD class (pure operators, lane access, `v128.const`, memory access, memory lane access
and `i8x16.shuffle`) a `Completeness.Frame.simd_*` lemma shows that `Wasm2.step` accepts the
independent `0xFD` encoding at a realized operand stack. `Frame.simd` combines them for every
independently encoded and typed SIMD instruction (Wasm 2.0).
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Pure SIMD operators accept every realization of their principal signature. -/
theorem Frame.simd_pure {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (subopcode : U32) (op : Simd.Operation)
    (bytes : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (hmap : Simd.pureMeaning subopcode.val = some op)
    (he : Leb128.Encoding bytes subopcode.val) (hb : Wasm1.BytesAt data st.core.pos bytes next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C op.instruction (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨rfl, rfl⟩ := op.principal C ins outs ht
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.readFixed.complete decoded
    op.signature.popTypes (some op.signature.output) f.core.outer f.core.operands front
    f.core.vals f.core.base_eq hsize (by
      simpa only [Simd.Signature.inputs_pop, decoded, Control.polymorphic, f.core.ctrls,
        List.getLast?_concat] using hr)
  have hread := hb.read_u32 subopcode he
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by simpa [Simd.Signature.outputs_pop, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn]
    rw [code.step_wasm2.simd, code.step_simd.eq_runs]
    simp [Simd.prefixStep, hread, Simd.subStep, Simd.pure_table, hmap,
      Simd.signature_fixed, CoreVisitor.run, hs, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch,
      code.OpVisitor.on_simd.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.simd_lane {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (subopcode : U32) (op : Simd.LaneOperation)
    (lane : U8) (prefixBytes : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (hmap : Simd.laneMeaning subopcode.val = some op)
    (he : Leb128.Encoding prefixBytes subopcode.val)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ [lane]) next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C (op.instruction (.mk_uN lane.val)) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hbound := op.bound C (.mk_uN lane.val) ins outs ht
  obtain ⟨rfl, rfl⟩ := op.principal C (.mk_uN lane.val) ins outs ht
  obtain ⟨middle, hprefix, hlane⟩ := hb.split
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.carryFixed.complete lane decoded
    (Simd.laneInputs op.runtime.1 op.replace) (Simd.laneOutput op.runtime.1 op.replace)
    f.core.outer f.core.operands front f.core.vals f.core.base_eq hsize (by
      simpa only [Simd.LaneOperation.inputs_pop, decoded, Control.polymorphic, f.core.ctrls,
        List.getLast?_concat] using hr)
  have hread := hprefix.read_u32 subopcode he
  have hlaneread := Simd.take_lane_complete {st.core with pos := middle} data op.runtime.2.1 lane next
    hlane (by simpa [Simd.LaneOperation.runtime, proj_uN_0] using hbound)
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by
        simpa [Simd.LaneOperation.outputs_pop, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.simd, code.step_simd.eq_runs]
    simp only [Simd.prefixStep, hread, bind_ok]
    rw [Simd.subStep.lane _ _ _ _ _ _ _ hmap, Simd.lane_fixed]
    simp [Simd.laneReader, hlaneread, CoreVisitor.run, hs, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_lane.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.simd_const {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (low high : U64)
    (prefixBytes lower upper : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (he : Leb128.Encoding prefixBytes 12)
    (hlower : FloatBits.Encoding 8 lower low.val) (hupper : FloatBits.Encoding 8 upper high.val)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ (lower ++ upper)) next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C (Simd.vectorConstant low high) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  obtain ⟨rfl, rfl⟩ := Simd.vectorConstant_principal C low high ins outs ht
  obtain ⟨middle, hprefix, hbits⟩ := hb.split
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.carryFixed.complete (low, high) decoded
    [] (some .V128) f.core.outer f.core.operands front f.core.vals f.core.base_eq hsize (by
      simpa only [Simd.inputTypes, List.reverse_nil, List.map_nil, decoded, Control.polymorphic,
        f.core.ctrls, List.getLast?_concat] using hr)
  have hread := hprefix.read_u32 12#u32 he
  have hbitsread := Simd.take_bits_complete {st.core with pos := middle} data low high
    lower upper next hlower hupper hbits
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by
        simpa [Simd.outputTypes, Translate.valueType, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.simd, code.step_simd.eq_runs]
    simp only [Simd.prefixStep, hread, bind_ok]
    rw [Simd.subStep.constant, Simd.const_fixed]
    simp [Simd.constReader, hbitsread, CoreVisitor.run, hs, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_const.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega


theorem Frame.simd_memory {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (subopcode : U32) (op : Simd.MemoryOperation)
    (arg : code.MemArg) (prefixBytes alignment offset : List U8)
    (next : Usize) (C : context) (front ins outs : List valtype)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0)
    (he : Leb128.Encoding prefixBytes subopcode.val)
    (ha : Leb128.Encoding alignment arg.align.val) (ho : Leb128.Encoding offset arg.offset.val)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ (alignment ++ offset)) next)
    (hmatch : EnvTranslation.Matches env semantic C)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
      (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hcond := op.conditions C arg 0#u8 ins outs ht
  obtain ⟨rfl, rfl⟩ := op.principal C (MemoryMeaning.memArg arg) (.mk_uN 0) ins outs ht
  obtain ⟨middle, hprefix, harg⟩ := hb.split
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.carryFixed.complete arg decoded
    (Simd.fullMemoryInputs op.store) (Simd.memoryOutput op.store)
    f.core.outer f.core.operands front f.core.vals f.core.base_eq hsize (by
      simpa only [op.inputs_full hfull, decoded, Control.polymorphic, f.core.ctrls,
        List.getLast?_concat] using hr)
  have hread := hprefix.read_u32 subopcode he
  have hargread := Wasm1.BytesAt.read_memarg {st.core with pos := middle} arg harg ha ho
  have hcheck := code.check_memory_and_alignment.complete env arg op.runtime.1
    (by simpa [hmatch.mems] using hcond.1) (by simpa [Simd.MemoryOperation.runtime] using hcond.2.1)
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by
        simpa [Simd.MemoryOperation.outputs_pop, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.simd, code.step_simd.eq_runs]
    simp only [Simd.prefixStep, hread, bind_ok]
    rw [Simd.subStep.memory _ _ _ _ _ _ _ hmap hfull, Simd.full_memory_fixed]
    simp [Simd.fullMemoryReader, hargread, hcheck, CoreVisitor.run, hs, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_memory.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.simd_memory_lane {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (subopcode : U32) (op : Simd.MemoryOperation)
    (arg : code.MemArg) (lane : U8) (prefixBytes alignment offset : List U8)
    (next : Usize) (C : context) (front ins outs : List valtype)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0)
    (he : Leb128.Encoding prefixBytes subopcode.val)
    (ha : Leb128.Encoding alignment arg.align.val) (ho : Leb128.Encoding offset arg.offset.val)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ (alignment ++ offset ++ [lane])) next)
    (hmatch : EnvTranslation.Matches env semantic C)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hcond := op.conditions C arg lane ins outs ht
  obtain ⟨rfl, rfl⟩ := op.principal C (MemoryMeaning.memArg arg) (.mk_uN lane.val) ins outs ht
  obtain ⟨middle, hprefix, harglane⟩ := hb.split
  obtain ⟨ending, harg, hlane⟩ := harglane.split
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.carryFixed.complete (arg, lane) decoded
    [.V128, .I32] (Simd.memoryOutput op.store)
    f.core.outer f.core.operands front f.core.vals f.core.base_eq hsize (by
      simpa only [op.inputs_lane hlaned, decoded, Control.polymorphic, f.core.ctrls,
        List.getLast?_concat] using hr)
  have hread := hprefix.read_u32 subopcode he
  have hargread := Wasm1.BytesAt.read_memarg {st.core with pos := middle} arg harg ha ho
  have hlaneread := Simd.take_lane_complete {st.core with pos := ending} data op.runtime.2.2 lane next
    hlane (by simpa [Simd.MemoryOperation.runtime] using hcond.2.2 hlaned)
  have hcheck := code.check_memory_and_alignment.complete env arg op.runtime.1
    (by simpa [hmatch.mems] using hcond.1) (by simpa [Simd.MemoryOperation.runtime] using hcond.2.1)
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by
        simpa [Simd.MemoryOperation.outputs_pop, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.simd, code.step_simd.eq_runs]
    simp only [Simd.prefixStep, hread, bind_ok]
    rw [Simd.subStep.memoryLane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed]
    simp [Simd.memoryLaneReader, hargread, hlaneread, hcheck, CoreVisitor.run, hs, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_memory_lane.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega



theorem Frame.simd_shuffle {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx : code.Context) (index : U32) (low high : U64)
    (prefixBytes lower upper : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (he : Leb128.Encoding prefixBytes 13)
    (hlower : FloatBits.Encoding 8 lower low.val) (hupper : FloatBits.Encoding 8 upper high.val)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ (lower ++ upper)) next)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C (Simd.shuffle low high) (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  have hbound := Simd.shuffle_bound C low high ins outs ht
  obtain ⟨rfl, rfl⟩ := Simd.shuffle_principal C low high ins outs ht
  obtain ⟨middle, hprefix, hbits⟩ := hb.split
  let decoded : code.OpIterState := {st.core with pos := next}
  obtain ⟨s, after, hs, hc, hp, hv, hl, hout⟩ := Simd.carryFixed.complete (low, high) decoded
    [.V128, .V128] (some .V128) f.core.outer f.core.operands front f.core.vals f.core.base_eq hsize (by
      simpa only [Simd.inputTypes, List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_assoc, Translate.valueType, decoded, Control.polymorphic,
        f.core.ctrls, List.getLast?_concat] using hr)
  have hread := hprefix.read_u32 13#u32 he
  have hbitsread := Simd.take_bits_complete {st.core with pos := middle} data low high
    lower upper next hlower hupper hbits
  have hscan := Simd.shuffle_complete {st.core with pos := middle} data (lower ++ upper) next
    hbits (by simp [hlower.1, hupper.1]) (by
      rw [Simd.shuffleIndices_encoding low high lower upper hlower hupper] at hbound
      intro b hb
      exact hbound (.mk_uN b.val) (List.mem_map.mpr ⟨b, hb, rfl⟩)) (.Ok (low, high), s)
    (by simp [Simd.shuffleFinish, hbitsread, hs, decoded])
  refine ⟨{st with core := s}, ?_, hp,
    ⟨f.core.output_of_same_ctrls hc hv (by
        simpa [Simd.outputTypes, Translate.valueType, decoded, Control.polymorphic] using hout),
      code.BodyState.blocks_eq_of_ctrls hc⟩, ?_⟩
  · rw [step.scalar_eq st data env ctx index 0xFD#u8 (by decide)]
    have hn : alloc.vec.Vec.len st.core.vals ≠ core.num.Usize.MAX := by scalar_tac
    rw [if_neg hn, code.step_wasm2.simd, code.step_simd.eq_runs]
    simp only [Simd.prefixStep, hread, bind_ok]
    rw [Simd.subStep.shuffle]
    simp [CoreVisitor.run, hscan, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_shuffle.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

/-- Every independently encoded and typed SIMD instruction is accepted. -/
theorem Frame.simd {st} (f : Frame st) (data : Slice U8) (env : metadata.Env)
    (ctx semantic : code.Context) (index : U32) (subopcode : U32) (op : instr)
    (prefixBytes immediate : List U8) (next : Usize) (C : context) (front ins outs : List valtype)
    (he : Leb128.Encoding prefixBytes subopcode.val) (hi : Simd.Immediate subopcode op immediate)
    (hb : Wasm1.BytesAt data st.core.pos (prefixBytes ++ immediate) next)
    (hmatch : EnvTranslation.Matches env semantic C)
    (hsize : st.core.vals.val.length < Usize.max)
    (ht : Instr_ok C op (.mk_functype (.mk_list ins) (.mk_list outs)))
    (hr : Sequence.Realizes f.core.current.polymorphic_base f.core.operands (front ++ ins)) :
    ∃ s, step st data env ctx index 0xFD#u8 = .ok (.Ok (), s) ∧ s.core.pos = next ∧
      f.Output (front ++ outs) s ∧ s.core.vals.val.length ≤ st.core.vals.val.length + 1 := by
  cases hi with
  | pure subopcode op hmap =>
    exact f.simd_pure data env ctx index subopcode op prefixBytes next C front ins outs
      hmap he (by simpa using hb) hsize ht hr
  | lane subopcode op lane hmap =>
    exact f.simd_lane data env ctx index subopcode op lane prefixBytes next C front ins outs
      hmap he hb hsize ht hr
  | memory subopcode op arg hmap hfull ha ho =>
    exact f.simd_memory data env ctx semantic index subopcode op arg prefixBytes _ _ next C front ins outs
      hmap hfull he ha ho hb hmatch hsize ht hr
  | memoryLane subopcode op arg lane hmap hlaned ha ho =>
    exact f.simd_memory_lane data env ctx semantic index subopcode op arg lane prefixBytes _ _ next C front ins outs
      hmap hlaned he ha ho hb hmatch hsize ht hr
  | constant low high hlo hhi =>
    exact f.simd_const data env ctx index low high prefixBytes _ _ next C front ins outs
      he hlo hhi hb hsize ht hr
  | shuffle low high hlo hhi =>
    exact f.simd_shuffle data env ctx index low high prefixBytes _ _ next C front ins outs
      he hlo hhi hb hsize ht hr

end Itasca.Wasm2.Completeness

end

/-! ## Reader -/

section

/-!
Shared exact source-prefix and operand effects for all fixed-operand SIMD readers.
Validator preservation projects the total reader specification; compiler inversion
retains the same read state and stack effect without any visitor premise.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.fixed_reader {data env locals index st}
    (p : Wasm2.Pending data env locals index st)
    (position : Usize)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType) (source : instr)
    (capacity : st.core.vals.val.length < Usize.max)
    (wf : wf_instr source)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) source)
    (typed : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C source (.mk_functype (.mk_list (Wasm2.Simd.inputTypes inputs))
        (.mk_list (Wasm2.Simd.outputTypes output))))
    (encoded : Wasm2.At data p.start (.plain source) position) :
    Wasm2.Simd.readFixed {st.core with pos := position} inputs output ⦃ r =>
      r.2.ctrls = st.core.ctrls ∧ r.2.pos = position ∧
      ∀ unit, r.1 = .Ok unit → ∃ values,
        Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values ∧
        Wasm2.ReaderPost p r.2 source p.current.ctrl.polymorphic_base values ⦄ := by
  obtain ⟨C,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have Cwf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩
      (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter _
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have poly : Control.polymorphic {st.core with pos := position} = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic,ctrls]
  apply WP.spec_mono (Wasm2.Simd.readFixed.segment {st.core with pos := position} inputs output
    outer p.current.vals stack physicalBase capacity)
  rintro ⟨result,out⟩ ⟨controls,cursor,values,valuesEq,length,fixed⟩
  dsimp only at controls cursor valuesEq fixed
  refine ⟨controls,cursor,?_⟩
  intro unit accepted
  cases unit
  dsimp only at accepted
  subst result
  have finalEffect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values :=
    by simpa only [poly] using fixed rfl
  have finalTyped := finalEffect.wasm2_prefix _ Cwf _ p.current.ops source prior wf (typed _ Cwf matched)
  have finalEncoded : Wasm2.At data p.start (.plain source) out.pos := cursor ▸ encoded
  have finalControls : out.ctrls.val = p.parents.map Wasm2.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa only [controls] using ctrls
  have finalBlocks : ({st with core := out} : code.BodyState).blocks.val =
      p.parents.map Wasm2.Frames.Saved.bt ++ [p.current.bt] := by simpa [controls,ctrls] using blocks
  refine ⟨values,finalEffect,?_⟩
  exact p.append_reader_context C outer spine header base out source
    p.current.ctrl.polymorphic_base values wf finalEncoded finalTyped finalControls finalBlocks valuesEq
    declared

theorem Pending.fixed_reader_accepted {data env locals index st}
    (p : Wasm2.Pending data env locals index st)
    (position : Usize) (out : code.OpIterState)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType) (source : instr)
    (capacity : st.core.vals.val.length < Usize.max)
    (wf : wf_instr source)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) source)
    (typed : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C source (.mk_functype (.mk_list (Wasm2.Simd.inputTypes inputs))
        (.mk_list (Wasm2.Simd.outputTypes output))))
    (encoded : Wasm2.At data p.start (.plain source) position)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out)) :
    out.ctrls = st.core.ctrls ∧ out.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        inputs output values ∧ Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values := by
  have effect := p.fixed_reader position inputs output source capacity wf declared typed encoded
  rw [read, WP.spec_ok] at effect
  exact ⟨effect.1, effect.2.1, effect.2.2 () rfl⟩

end Itasca.Wasm2

end

/-! ## Sound -/

section

/-!
# Preservation for SIMD instructions

`Pending.simd` shows that the extracted `code.step_simd` preserves the body invariant `Pending`
for every SIMD instruction (Wasm 2.0). It combines `Pending.simd_pure`, `Pending.simd_lane`,
`Pending.simd_const`, `Pending.simd_memory`, `Pending.simd_memory_lane` and `Pending.simd_shuffle`,
which rest on `Pending.fixed`, the extension of the typed prefix by a fixed operand effect.
-/

open Aeneas Aeneas.Std

namespace Itasca.Wasm2

private theorem lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- A fixed operand effect extends the independently typed prefix in the active frame. -/
theorem Pending.fixed {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (v : V)
    (inputs : List wasm_types.ValueType) (output : Option wasm_types.ValueType) (op : instr)
    (hw : wf_instr op)
    (hdecl : DeclaredReferences.Instruction (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) op)
    (ht : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals, p.ft.results⟩ C → Instr_ok C op
      (.mk_functype (.mk_list (Simd.inputTypes inputs)) (.mk_list (Simd.outputTypes output))))
    (pos : Usize) (hsize : st.core.vals.val.length < Usize.max)
    (hook : V → code.OpIterState → Unit → Result (core.result.Result Unit error.VisitError × V))
    (hhook : ∀ s a, ∃ reply v', hook v s a = .ok (reply, v'))
    (hencoded : At data p.start (.plain op) pos) :
    CoreVisitor.run (Simd.readFixed {st.core with pos := pos} inputs output) hook v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  apply WP.spec_mono (CoreVisitor.run.spec _ hook v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ hhook)
  · intro r effect accepted
    exact (effect.2 accepted).choose_spec
  · apply WP.spec_mono (p.fixed_reader pos inputs output op hsize hw hdecl ht hencoded)
    intro r effect
    refine ⟨trivial, ?_⟩
    intro unit accepted
    obtain ⟨values, _, post⟩ := effect.2.2 unit accepted
    exact post.after


theorem Pending.simd_pure {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.Operation)
    (hmap : Simd.pureMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : At data p.start (.plain op.instruction) pos) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  simp only [Simd.subStep, Simd.pure_table, hmap, Option.map_some, bind_ok]
  rw [Simd.signature_fixed]
  apply p.fixed v op.signature.popTypes (some op.signature.output) op.instruction op.wellFormed (op.declared _)
    (fun C hC _ => by simpa [Simd.Signature.inputs_pop, Simd.Signature.outputs_pop] using op.typed C hC)
    pos hsize _ (fun s _ => hv.on_simd v s subopcode) hencoded

theorem Pending.simd_lane {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.LaneOperation)
    (hmap : Simd.laneMeaning subopcode.val = some op) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ lane next, Wasm1.BytesAt data pos [lane] next →
      At data p.start (.plain (op.instruction (.mk_uN lane.val))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.lane _ _ _ _ _ _ _ hmap, Simd.lane_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hlane⟩ := WP.spec_imp_exists
    (Simd.take_lane_spec {st.core with pos := pos} data op.runtime.2.1)
  have hstate : decoded = {st.core with pos := decoded.pos} := by
    exact Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.laneReader]
  rw [hd]
  simp only [bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok lane =>
    obtain ⟨hbound, hbytes⟩ := hlane lane rfl
    rw [hstate, Simd.carryFixed.run]
    apply p.fixed v (Simd.laneInputs op.runtime.1 op.replace)
      (Simd.laneOutput op.runtime.1 op.replace) (op.instruction (.mk_uN lane.val))
      (op.wellFormed _ (lane_wf lane)) (op.declared _ _)
      (fun C hC _ => ?_) decoded.pos hsize _ (fun s _ => hv.on_simd_lane v s subopcode lane)
      (hencoded lane decoded.pos hbytes)
    simpa only [Simd.LaneOperation.inputs_pop, Simd.LaneOperation.outputs_pop] using
      op.typed C (.mk_uN lane.val) hC (lane_wf lane)
        (by simpa [Simd.LaneOperation.runtime, proj_uN_0] using hbound)


theorem Pending.simd_const {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.vectorConstant low high)) next) :
    Simd.subStep visitor {st.core with pos := pos} data env 12#u32 v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.constant, Simd.const_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hc, hvals, hbits⟩ := WP.spec_imp_exists
    (Simd.take_bits_spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.constReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, high⟩ := pair
    rw [hstate, Simd.carryFixed.run]
    apply p.fixed v [] (some .V128) (Simd.vectorConstant low high)
      (Simd.vectorConstant_wf low high) (Simd.vectorConstant_declared _ low high)
      (fun C hC _ => Simd.vectorConstant_typed C low high hC)
      decoded.pos hsize _ (fun s _ => hv.on_simd_const v s low high)
      (hencoded low high decoded.pos (hbits low high rfl))


theorem Pending.simd_memory {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hfull : op.laneCount = 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.memory _ _ _ _ _ _ _ hmap hfull, Simd.full_memory_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  have hstate : decoded = {st.core with pos := decoded.pos} :=
    Simd.state_of_stacks decoded st.core hvals hc
  simp only [Simd.fullMemoryReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨res, hcheck, hc⟩ := WP.spec_imp_exists
      (code.check_memory_and_alignment.spec env arg op.runtime.1)
    dsimp only
    rw [hcheck]
    simp only [bind_ok]
    cases res with
    | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok _ =>
      rw [hstate, Simd.carryFixed.run]
      apply p.fixed v (Simd.fullMemoryInputs op.store) (Simd.memoryOutput op.store)
        (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
        (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) (by constructor; decide)) (op.declared _ _ _)
        (fun C hC hm => ?_) decoded.pos hsize _ (fun s _ => hv.on_simd_memory v s subopcode arg)
        (hencoded arg middle decoded.pos halign hoffset)
      simpa only [op.inputs_full hfull, Simd.MemoryOperation.outputs_pop, UScalar.ofNatCore_val_eq] using
        op.typed_runtime C env ⟨locals, p.ft.results⟩ hC hm arg 0#u8 hc.1
          (by simpa [Simd.MemoryOperation.runtime] using hc.2) (by simp [hfull])

theorem Pending.simd_memory_lane {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (subopcode : U32) (op : Simd.MemoryOperation)
    (hmap : Simd.memoryMeaning subopcode.val = some op) (hlaned : op.laneCount ≠ 0) (pos : Usize)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ arg middle ending lane next, Leb128.Decoded data pos arg.align middle →
      Leb128.Decoded data middle arg.offset ending → Wasm1.BytesAt data ending [lane] next →
      At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) next) :
    Simd.subStep visitor {st.core with pos := pos} data env subopcode v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.memoryLane _ _ _ _ _ _ _ hmap hlaned, Simd.memory_lane_fixed]
  obtain ⟨⟨res, decoded⟩, hd, hvals, hc, harg⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := pos} data)
  simp only [Simd.memoryLaneReader, hd, bind_ok, Std.uncurry]
  cases res with
  | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok arg =>
    obtain ⟨middle, halign, hoffset⟩ := harg
    obtain ⟨⟨res, laned⟩, hd, hc2, hvals2, hlane⟩ := WP.spec_imp_exists
      (Simd.take_lane_spec decoded data op.runtime.2.2)
    simp only [hd, bind_ok, Std.uncurry]
    cases res with
    | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok lane =>
      obtain ⟨hbound, hbytes⟩ := hlane lane rfl
      have hstate : laned = {st.core with pos := laned.pos} :=
        Simd.state_of_stacks laned st.core (hvals2.trans hvals) (hc2.trans hc)
      obtain ⟨res, hcheck, hc⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env arg op.runtime.1)
      rw [hcheck]
      simp only [bind_ok]
      cases res with
      | Err e => simp [CoreVisitor.run, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok _ =>
        rw [hstate, Simd.carryFixed.run]
        apply p.fixed v [.V128, .I32] (Simd.memoryOutput op.store)
          (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
          (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) (lane_wf lane)) (op.declared _ _ _)
          (fun C hC hm => ?_) laned.pos hsize _ (fun s _ => hv.on_simd_memory_lane v s subopcode arg lane)
          (hencoded arg middle decoded.pos lane laned.pos halign hoffset hbytes)
        simpa only [op.inputs_lane hlaned, Simd.MemoryOperation.outputs_pop] using
          op.typed_runtime C env ⟨locals, p.ft.results⟩ hC hm arg lane hc.1
            (by simpa [Simd.MemoryOperation.runtime] using hc.2)
            (fun _ => by simpa [Simd.MemoryOperation.runtime] using hbound)


/-- A shuffle's scanner proves the lane limits before its fixed binary stack effect. -/
theorem Pending.shuffle_reader {data env locals index st}
    (p : Pending data env locals index st) (pos : Usize) (hpos : pos.val ≤ data.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.shuffle low high)) next) :
    code.read_simd_shuffle {st.core with pos := pos} data ⦃ r =>
      ∀ low high, r.1 = .Ok (low, high) →
        Simd.BitsDecoded data pos low high r.2.pos ∧
        (∀ lane ∈ Simd.shuffleIndices low high, proj_uN_0 lane < 32) ∧
        r.2.ctrls = st.core.ctrls ∧ ∃ after,
          Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [.V128, .V128] (some .V128) after ∧
          ReaderPost p r.2 (Simd.shuffle low high) p.current.ctrl.polymorphic_base after ⦄ := by
  obtain ⟨C, outer, spine, header, base, typed, ctrls, blocks, stack⟩ := id p.opened
  let decoded := {st.core with pos := pos}
  have hC := Frames.enter_wf C (spine.context_wf (EnvTranslation.context_wf env ⟨locals, p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have hbase : (Control.base decoded).val = outer.length := by simp [decoded, Control.base, ctrls, base]
  have hpoly : Control.polymorphic decoded = p.current.ctrl.polymorphic_base := by
    simp [decoded, Control.polymorphic, ctrls]
  apply WP.spec_mono (Simd.shuffle_segment decoded data outer p.current.vals stack hbase hsize hpos)
  rintro ⟨res, s⟩ hpost
  intro low high hok
  obtain ⟨hc, after, hvals, hbits, hbound, heffect⟩ := hpost low high hok
  dsimp only at hc hvals hbits hbound heffect
  have htyped := heffect.wasm2_prefix _ hC _ p.current.ops (Simd.shuffle low high)
    (by simpa [hpoly] using typed) (Simd.shuffle_wf low high)
    (Simd.shuffle_typed _ low high hC hbound)
  refine ⟨hbits, hbound, hc, after, (by simpa [hpoly] using heffect), ?_⟩
  apply p.append_reader_context C outer spine header base s (Simd.shuffle low high)
    p.current.ctrl.polymorphic_base after (Simd.shuffle_wf low high)
    (hencoded low high s.pos hbits) (by simpa [hpoly] using htyped) ?_ ?_ hvals
    (Simd.shuffle_declared _ low high)
  · simpa [hc, decoded] using ctrls
  · simpa [code.BodyState.blocks_eq_of_ctrls (show s.ctrls = st.core.ctrls from hc)] using blocks

/-- A shuffle's scanner proves the lane limits before its fixed binary stack effect. -/
theorem Pending.simd_shuffle {data env locals index st}
    (p : Pending data env locals index st) {V : Type} (visitor : code.OpVisitor V) (v : V)
    (hv : FullVisitor.Total visitor) (pos : Usize) (hpos : pos.val ≤ data.length)
    (hsize : st.core.vals.val.length < Usize.max)
    (hencoded : ∀ low high next, Simd.BitsDecoded data pos low high next →
      At data p.start (.plain (Simd.shuffle low high)) next) :
    Simd.subStep visitor {st.core with pos := pos} data env 13#u32 v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [Simd.subStep.shuffle]
  apply WP.spec_mono (CoreVisitor.run.spec _ _ v (fun _ => True)
    (fun _ s => p.After {st with core := s}) ?_ (fun s a => hv.on_simd_shuffle v s a.1 a.2))
  · intro r hr hok
    exact (hr.2 hok).choose_spec
  · apply WP.spec_mono (p.shuffle_reader pos hpos hsize hencoded)
    intro r effect
    refine ⟨trivial, ?_⟩
    rintro ⟨low, high⟩ accepted
    obtain ⟨_, _, _, _, _, post⟩ := effect low high accepted
    exact post.after

/-- The complete SIMD prefix dispatcher preserves the independently encoded typed body. -/
theorem Pending.simd {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (v : V) (hv : FullVisitor.Total visitor)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = 0xFD#u8) :
    code.step_simd visitor st.core data env v ⦃ r =>
      r.1 = .Ok () → p.After {st with core := r.2.1} ⦄ := by
  rw [code.step_simd.eq_runs]
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Simd.prefixStep, hr, bind_ok]
  cases r with
  | Err e => simp
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
      apply p.simd_const visitor v hv next hsize
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.constant low high hlo hhi) hspan
    by_cases hshuffle : subopcode = 13#u32
    · subst subopcode
      apply p.simd_shuffle visitor v hv next hb hsize
      intro low high ending hbits
      obtain ⟨lower, upper, hlo, hhi, hspan⟩ := hbits
      exact henc _ _ _ (.shuffle low high hlo hhi) hspan
    cases hp : Simd.pureMeaning subopcode.val with
    | some op =>
      exact p.simd_pure visitor v hv subopcode op hp next hsize
        (henc _ _ _ (.pure subopcode op hp) (Wasm1.BytesAt.nil data next hb))
    | none =>
      cases hl : Simd.laneMeaning subopcode.val with
      | some op =>
        apply p.simd_lane visitor v hv subopcode op hl next hsize
        intro lane ending hspan
        exact henc _ _ _ (.lane subopcode op lane hl) hspan
      | none =>
        cases hm : Simd.memoryMeaning subopcode.val with
        | some op =>
          by_cases hfull : op.laneCount = 0
          · apply p.simd_memory visitor v hv subopcode op hm hfull next hsize
            intro arg middle ending halign hoffset
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memory subopcode op arg hm hfull ha4 ho4)
              ((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append ⟨ho1, ho2, ho3⟩)
          · apply p.simd_memory_lane visitor v hv subopcode op hm hfull next hsize
            intro arg middle ending lane final halign hoffset hspan
            obtain ⟨alignment, ha1, ha2, ha3, ha4⟩ := halign
            obtain ⟨offset, ho1, ho2, ho3, ho4⟩ := hoffset
            exact henc _ _ _ (.memoryLane subopcode op arg lane hm hfull ha4 ho4)
              (((show Wasm1.BytesAt data next alignment middle from ⟨ha1, ha2, ha3⟩).append
                ⟨ho1, ho2, ho3⟩).append hspan)
        | none =>
          simp only [Simd.subStep, Simd.pure_table, Simd.lane_table, Simd.memory_table,
            hp, hl, hm, Option.map_none, bind_ok]
          split <;> simp_all
          · exact False.elim (hconstant (by with_unfolding_all rfl))
          · exact False.elim (hshuffle (by with_unfolding_all rfl))

end Itasca.Wasm2

end
