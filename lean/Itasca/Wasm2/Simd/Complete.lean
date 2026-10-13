import Itasca.Wasm2.Simd.Shuffle
import Itasca.Handler.EnvComplete
import Itasca.Wasm2.Simd.MemoryReaders
import Itasca.Wasm2.Simd.Dispatch
import Itasca.Wasm2.Simd.Decode
import Itasca.Binary.Wasm2.SimdBitsMeaning
import Itasca.Wasm2.Simd.Visitor
import Itasca.Wasm2.Step.Context
import Itasca.Wasm2.Complete.Frame

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Pure SIMD operators accept every realization of their principal signature. -/
theorem Frame.simd_pure {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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
      code.EmptyOpVisitor.Insts.ItascaCodeOpVisitor, code.OpVisitor.on_simd.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

theorem Frame.simd_lane {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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

theorem Frame.simd_const {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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


theorem Frame.simd_memory {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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

theorem Frame.simd_memory_lane {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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



theorem Frame.simd_shuffle {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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
    simp [CoreVisitor.run, hscan, decoded, code.visit,
      core.result.Result.Insts.CoreOpsTry.branch, code.OpVisitor.on_simd_shuffle.default]
  · simp only [hv, f.core.vals, List.length_append]
    omega

/-- Every independently encoded and typed SIMD instruction is accepted. -/
theorem Frame.simd {st} (f : Frame st) (data : Slice U8) (env : module.Env)
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
