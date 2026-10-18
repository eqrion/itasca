import Exec.Code.Body.Reader.Simd.ReaderSimdLane
import Exec.Code.Body.Reader.Simd.ReaderSimdEmissions
import Exec.Code.Local.Lowering.Simd.SimdCallbacks
import Exec.Code.Body.Reader.Simd.SimdReaderMeaning
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem reader_emit_simd_lane_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.LaneOperation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.laneMeaning sub.val = some op)
    (opcode : U16) (number : opcode.val = 512 + sub.val) (C : context)
    (known : ConcreteStack st.core.vals.val) (monomorphic : p.current.ctrl.polymorphic_base = false)
    (contextLocals : C.LOCALS = compilerLocals before)
    (layout : CompilerLayout before (Sequence.stackTypes st.core.vals.val))
    (reachable : before.reachable = true)
    (codeFits : before.function.code.val.length < Usize.max)
    (sourceFits : before.function.source_offsets.val.length < Usize.max)
    (coordinateFits : before.function.body_start.val + before.next_source.val ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 0xfd#u8 before = .ok (.Ok (),out,after)) :
    CompilerOrdinaryStable before after ∧ SourceProgress before after ∧ after.next_source = out.core.pos ∧
    after.function.v128_pool = before.function.v128_pool ∧
    ∃ (lane : U8), ∃ front values emitted,
      after.function.simd.val = before.function.simd.val ++ [simdImmediate sub (UScalar.cast .U32 lane) 0#u128] ∧
      Sequence.stackTypes st.core.vals.val = front ++ op.inputs ∧
      ReaderPostWasm2 p out.core (op.instruction (.mk_uN lane.val)) p.current.ctrl.polymorphic_base values ∧
      TypedLowered before after out.core.vals.val emitted (front ++ op.outputs) ∧
      SimdEmission after.function.simd.val after.function.v128_pool.val C
        (front ++ op.inputs) (op.instruction (.mk_uN lane.val)) [emitted] (front ++ op.outputs) := by
  obtain ⟨capacity,_⟩ := simd_prefix_success (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
    st out data env ctx index before after accepted
  obtain ⟨lane,position,laneBound,span,callback,read,controls,cursor,values,effect,post⟩ := reader_simd_lane_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx sub next op decoded meaning byte accepted
  have retained := simd_lane_callback_meaning C sub op lane meaning
  have bound := retained.opcode_bound
  have nonconstant := retained.not_constant
  rw [compiler_simd_lane_callback ops before out.core sub opcode bound number lane] at callback
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.laneInputs op.runtime.1 op.replace)) (op.instruction (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.laneOutput op.runtime.1 op.replace)) := by
    simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop] using retained
  obtain ⟨ordinary,sources,cursor,simd,pool,front,emitted,oldTypes,lowered,emission⟩ :=
    reader_simd_fixed_emission p ops law before after out.core C opcode sub (UScalar.cast .U32 lane) 0#u32 0#u128
      number bound nonconstant normalized post effect read known monomorphic capacity contextLocals layout reachable
      codeFits sourceFits coordinateFits callback
  refine ⟨ordinary,sources,cursor,pool,lane,front,values,emitted,simd,?_,post,?_,?_⟩
  · simpa only [Wasm2.Simd.LaneOperation.inputs_pop] using oldTypes
  · simpa only [Wasm2.Simd.LaneOperation.outputs_pop] using lowered
  · simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop] using emission
end Exec.Code
