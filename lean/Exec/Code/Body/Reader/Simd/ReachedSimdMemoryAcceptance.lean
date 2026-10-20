import Exec.Code.Body.Reader.Simd.SimdPrefixAcceptance
import Exec.Code.Body.Reader.Simd.ReaderSimdAcceptance
import Exec.Code.Body.Reader.Simd.ReaderSimdEvents
import Exec.Code.Body.Reader.Acceptance.RecordedReaderAcceptance
import Exec.Code.Local.Capacity.SimdCallbacksAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- The actual memory SIMD reader accepts from its independent source
memory rule and the retained live compiler layout, including dead code. -/
theorem reached_profile_simd_memory_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (full : op.laneCount = 0)
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
  obtain ⟨arg,middle,position,alignment,offset,checked,sourceCalled,read,controls,cursor,values,effect,post⟩ :=
    reader_simd_memory_wasm2 p recorder before after out ctx sub next op decoded meaning full byte reference
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_callback_meaning C sub op arg memory meaning full available
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      (Wasm2.Simd.inputTypes (Wasm2.Simd.fullMemoryInputs op.store))
      (op.instruction (MemoryMeaning.memArg arg) (.mk_uN 0))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_full full,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_memory sub arg)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory compiler out.core sub arg ⦃ _ ⦄
    rw [compiler_simd_memory_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simdCompilerOpcode_val sub bounded) arg]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub arg.offset arg.align 0#u128 (simdCompilerOpcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.memory _ _ _ _ _ _ op meaning full] at raw ⊢
  exact recorded_reader_available (if op.store then code.read_store {st.core with pos := next} data env .V128 op.runtime.1
      else code.read_load {st.core with pos := next} data env .V128 op.runtime.1)
    (fun actual => .simd_memory sub actual) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_memory sub arg)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- The actual memory_lane SIMD reader accepts from its independent source
memory rule and the retained live compiler layout, including dead code. -/
theorem reached_profile_simd_memory_lane_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (sub : U32) (next : Usize) (op : Wasm2.Simd.MemoryOperation)
    (decoded : Leb128.Decoded data st.core.pos sub next)
    (meaning : Wasm2.Simd.memoryMeaning sub.val = some op)
    (laned : op.laneCount ≠ 0)
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
  obtain ⟨arg,middle,ending,lane,position,alignment,offset,span,laneBound,checked,sourceCalled,read,controls,cursor,values,effect,post⟩ :=
    reader_simd_memory_lane_wasm2 p recorder before after out ctx sub next op decoded meaning laned byte reference
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_lane_callback_meaning C sub op arg lane memory meaning laned available
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      (Wasm2.Simd.inputTypes [.V128,.I32]) (op.instruction (MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (Wasm2.Simd.outputTypes (Wasm2.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_lane laned,Wasm2.Simd.MemoryOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_memory_lane sub arg lane)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane compiler out.core sub arg lane ⦃ _ ⦄
    rw [compiler_simd_memory_lane_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simdCompilerOpcode_val sub bounded) arg lane]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub arg.offset arg.align (UScalar.cast .U128 lane) (simdCompilerOpcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Wasm2.Simd.subStep.memoryLane _ _ _ _ _ _ op meaning laned] at raw ⊢
  exact recorded_reader_available (code.read_simd_memory_lane {st.core with pos := next} data env op.runtime.1 op.store op.runtime.2.2)
    (fun actual : code.MemArg × U8 => .simd_memory_lane sub actual.1 actual.2) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_memory_lane sub arg lane)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Exec.Code
