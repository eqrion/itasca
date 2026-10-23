import Exec.Code.Body.Reader.Simd.SimdPrefixAcceptance
import Exec.Code.Body.Reader.Simd.ReaderSimdAcceptance
import Exec.Code.Body.Reader.Simd.ReaderSimdEvents
import Exec.Code.Body.Reader.Acceptance.RecordedReaderAcceptance
import Exec.Code.Local.Capacity.SimdCallbacksAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Replay the actual pure SIMD reader from its independently accepted
source event, with bounded real callback allocation and instruction charges. -/
theorem reached_profile_simd_pure_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.Operation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.pureMeaning sub.val = some op)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨sourceCalled,read,controls,position,values,effect,post⟩ := reader_simd_pure_wasm2 p
    recorder before after out ctx sub next op decoded meaning byte reference
  have bounded := Wasm2.Simd.pure_bound meaning
  have retained : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128)
      (Wasm2.Simd.inputTypes op.signature.popTypes) op.instruction
      (Wasm2.Simd.outputTypes (some op.signature.output)) := by
    simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop] using
      (SimdImmediateMeaning.pure sub (simdImmediate sub 0#u32 0#u128) op meaning : SimdImmediateMeaning C _ _ _ _ _)
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd sub)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd compiler out.core sub ⦃ _ ⦄
    rw [compiler_simd_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded (simdCompilerOpcode_val sub bounded)]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub 0#u32 0#u32 0#u128 (simdCompilerOpcode_val sub bounded) retained post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.pure _ _ _ _ _ _ op meaning] at raw ⊢
  exact recorded_reader_available (code.read_simd_signature {st.core with pos := next} op.signature.runtime)
    (fun (_ : Unit) => .simd sub) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd sub)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- Replay the actual lane SIMD reader from its independently accepted
source event, with bounded real callback allocation and instruction charges. -/
theorem reached_profile_simd_lane_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.LaneOperation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.laneMeaning sub.val = some op)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨lane,position,laneBound,span,sourceCalled,read,controls,cursor,values,effect,post⟩ := reader_simd_lane_wasm2 p
    recorder before after out ctx sub next op decoded meaning byte reference
  have retained := simd_lane_callback_meaning C sub op lane meaning
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.laneInputs op.runtime.1 op.replace)) (op.instruction (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.laneOutput op.runtime.1 op.replace)) := by
    simpa only [Wasm2.Simd.LaneOperation.inputs_pop,Wasm2.Simd.LaneOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_lane sub lane)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane compiler out.core sub lane ⦃ _ ⦄
    rw [compiler_simd_lane_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simdCompilerOpcode_val sub bounded) lane]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub (UScalar.cast .U32 lane) 0#u32 0#u128 (simdCompilerOpcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.lane _ _ _ _ _ _ op meaning] at raw ⊢
  exact recorded_reader_available
    (code.read_simd_lane {st.core with pos := next} data op.runtime.1 op.runtime.2.1 op.replace)
    (fun actual => .simd_lane sub actual) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_lane sub lane)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Exec.Code
