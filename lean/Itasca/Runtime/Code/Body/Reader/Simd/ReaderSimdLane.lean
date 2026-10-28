import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdPure
namespace Itasca.Runtime.Code
set_option maxRecDepth 4096
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

private theorem simd_lane_wf (lane : U8) : wf_uN 8 (.mk_uN lane.val) := by
  constructor
  scalar_tac

/-- A successful fixed checker returns exactly its already decoded payload. -/
theorem simd_carry_success {A : Type} (value result : A) (st out : code.OpIterState)
    (inputs : List types.ValueType) (output : Option types.ValueType)
    (accepted : Wasm2.Simd.carryFixed value st inputs output = .ok (.Ok result,out)) :
    value = result ∧ Wasm2.Simd.readFixed st inputs output = .ok (.Ok (),out) := by
  unfold Wasm2.Simd.carryFixed at accepted
  obtain ⟨⟨reply,after⟩,read,tail⟩ := bind_ok_inv _ _ _ accepted
  cases reply with
  | Err error => simp [uncurry_apply_pair] at tail
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at tail
    obtain ⟨rfl,rfl⟩ := tail
    exact ⟨rfl,read⟩

/-- Accepted SIMD lane readers retain the literal lane, its bound, the exact
callback, and the source zipper after the fixed operand check. -/
theorem reader_simd_lane_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.LaneOperation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.laneMeaning subopcode.val = some op)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ lane position, lane.val < op.count ∧ Wasm1.BytesAt data next [lane] position ∧
      visitor.on_simd_lane before out.core subopcode lane = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position}
        (Wasm2.Simd.laneInputs op.runtime.1 op.replace) (Wasm2.Simd.laneOutput op.runtime.1 op.replace) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        (Wasm2.Simd.laneInputs op.runtime.1 op.replace) (Wasm2.Simd.laneOutput op.runtime.1 op.replace) values ∧
        ReaderPostWasm2 p out.core (op.instruction (.mk_uN lane.val)) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.lane visitor _ data env subopcode before op meaning] at run
  obtain ⟨lane,read,callback⟩ := reader_run_success _ _ _ _ _ run
  rw [Wasm2.Simd.lane_fixed] at read
  obtain ⟨⟨reply,middle⟩,take,controls,values,laneInfo⟩ := WP.spec_imp_exists
    (Wasm2.Simd.take_lane_spec {st.core with pos := next} data op.runtime.2.1)
  dsimp only at controls values laneInfo
  cases reply with
  | Err error => simp [Wasm2.Simd.laneReader,take] at read
  | Ok value =>
    simp only [Wasm2.Simd.laneReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨valueEq,fixed⟩ := simd_carry_success value lane middle out.core _ _ read
    subst value
    obtain ⟨laneBound,span⟩ := laneInfo lane rfl
    have middleEq : middle = {st.core with pos := middle.pos} := Wasm2.Simd.state_of_stacks middle st.core values controls
    rw [middleEq] at fixed
    have bound : lane.val < op.count := by simpa only [Wasm2.Simd.LaneOperation.runtime,U8.ofNatCore_val_eq] using laneBound
    have laneWf := simd_lane_wf lane
    have encoded : Wasm2.At data p.start (.plain (op.instruction (.mk_uN lane.val))) middle.pos := by
      obtain ⟨bytes,first,last,within,leb⟩ := decoded
      exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.lane subopcode op lane meaning))
        ((show Wasm1.BytesAt data st.core.pos bytes next from ⟨first,last,within⟩).append span)
    refine ⟨lane,middle.pos,bound,span,callback,fixed,?_⟩
    exact reader_simd_fixed_post p middle.pos out.core _ _ (op.instruction (.mk_uN lane.val))
      capacity (op.wellFormed _ laneWf) (op.declared _ _)
      (fun C wf _ => by simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop]
          using op.typed C (.mk_uN lane.val) wf laneWf bound) encoded fixed

end Itasca.Runtime.Code
