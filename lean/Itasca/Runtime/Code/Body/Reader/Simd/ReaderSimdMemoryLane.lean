import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdLane
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

private theorem simd_memory_lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- Lane SIMD memory readers retain both encoded immediates, validated memory
availability and alignment, the exact callback, and the source prefix. -/
theorem reader_simd_memory_lane_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.memoryMeaning subopcode.val = some op) (laned : op.laneCount ≠ 0)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ arg middle ending lane position, Leb128.Decoded data next arg.align middle ∧
      Leb128.Decoded data middle arg.offset ending ∧
      Wasm1.BytesAt data ending [lane] position ∧ lane.val < op.laneCount ∧
      code.check_memory_and_alignment env arg op.runtime.1 = .ok (.Ok ()) ∧
      visitor.on_simd_memory_lane before out.core subopcode arg lane = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [.V128, .I32]
        (Wasm2.Simd.memoryOutput op.store) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [.V128, .I32] (Wasm2.Simd.memoryOutput op.store) values ∧
        ReaderPostWasm2 p out.core (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
          p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.memoryLane visitor _ data env subopcode before op meaning laned] at run
  obtain ⟨⟨arg,lane⟩,read,callback⟩ := reader_run_success _ _ _ _ _ run
  rw [Wasm2.Simd.memory_lane_fixed] at read
  obtain ⟨⟨reply,parsed⟩,take,values,controls,argInfo⟩ := WP.spec_imp_exists
    (code.read_memarg.spec {st.core with pos := next} data)
  dsimp only at controls values argInfo
  cases reply with
  | Err error => simp [Wasm2.Simd.memoryLaneReader,take] at read
  | Ok decodedArg =>
    simp only [Wasm2.Simd.memoryLaneReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨middle,alignment,offset⟩ := argInfo
    obtain ⟨⟨laneReply,finished⟩,takeLane,laneControls,laneValues,laneInfo⟩ := WP.spec_imp_exists
      (Wasm2.Simd.take_lane_spec parsed data op.runtime.2.2)
    rw [takeLane] at read
    cases laneReply with
    | Err error => simp at read
    | Ok decodedLane =>
      simp only [bind_ok,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch] at read
      obtain ⟨result,check,checked⟩ := WP.spec_imp_exists
        (code.check_memory_and_alignment.spec env decodedArg op.runtime.1)
      rw [check] at read
      cases result with
      | Err error => simp at read
      | Ok unitValue =>
        cases unitValue
        simp only [bind_ok,core.result.Result.Insts.CoreOpsTry.branch] at read
        obtain ⟨argEq,fixed⟩ := simd_carry_success (decodedArg,decodedLane) (arg,lane) finished out.core _ _ read
        cases argEq
        obtain ⟨laneBound,laneSpan⟩ := laneInfo lane rfl
        have laneWf : wf_uN 8 (.mk_uN lane.val) := by exact simd_memory_lane_wf lane
        have parsedEq : finished = {st.core with pos := finished.pos} := Wasm2.Simd.state_of_stacks finished st.core (laneValues.trans values) (laneControls.trans controls)
        rw [parsedEq] at fixed
        have encoded : Wasm2.At data p.start (.plain (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))) finished.pos := by
          obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
          obtain ⟨alignBytes,af,al,ab,ae⟩ := alignment
          obtain ⟨offsetBytes,of,ol,ob,oe⟩ := offset
          apply Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.memoryLane subopcode op arg lane meaning laned ae oe))
          simpa only [List.append_assoc] using
            ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append
              ((show Wasm1.BytesAt data next alignBytes middle from ⟨af,al,ab⟩).append ((show Wasm1.BytesAt data middle offsetBytes parsed.pos from ⟨of,ol,ob⟩).append laneSpan)))
        refine ⟨arg,middle,parsed.pos,lane,finished.pos,alignment,offset,laneSpan,by simpa only [Wasm2.Simd.MemoryOperation.runtime,U8.ofNatCore_val_eq] using laneBound,check,callback,fixed,?_⟩
        exact reader_simd_fixed_post p finished.pos out.core _ _ _ capacity
          (op.wellFormed _ _ (MemoryMeaning.memArg_wf arg) laneWf) (op.declared _ _ _)
          (fun C wf matched => by
            simpa only [op.inputs_lane laned,Wasm2.Simd.MemoryOperation.outputs_pop,UScalar.ofNatCore_val_eq] using
              op.typed_runtime C env ⟨locals,p.ft.results⟩ wf matched arg lane checked.1
                (by simpa [Wasm2.Simd.MemoryOperation.runtime] using checked.2) (fun _ => by simpa only [Wasm2.Simd.MemoryOperation.runtime,U8.ofNatCore_val_eq] using laneBound)) encoded fixed
end Itasca.Runtime.Code
