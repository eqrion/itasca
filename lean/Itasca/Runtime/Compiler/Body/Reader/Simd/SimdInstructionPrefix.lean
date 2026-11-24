import Itasca.Runtime.Compiler.Body.Simd.CallbackMeaning
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdEmissions
import Itasca.Runtime.Compiler.Local.Capacity.ConditionalAndSimdAvailability
import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdCallbackPublication
import Itasca.Runtime.Compiler.Body.Reader.Simd.Dispatch
import Itasca.Runtime.Compiler.Body.Reader.Acceptance.RecordedAcceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedCompilerLedger
import Itasca.Runtime.Compiler.Local.Capacity.CallbackBudgets
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.IndependentBodyDemand
import Itasca.Runtime.Compiler.Body.Relations.Checking.ExecutableInstructionPrefix
import Itasca.Runtime.Compiler.Local.Checking.ScopeInstructionPrefixes
import Itasca.Runtime.Compiler.Body.Reader.Replay.SingleCallbackExtended
import Itasca.Body.Trace.Refinement

/-!
Proofs for Runtime / Compiler / Body / Reader / Simd.

This module collects SimdInstructionPrefix, SingleCallbackSimd.
Each section documents its contracts and consumers.
-/

/-! ## SimdInstructionPrefix -/

section

open Itasca.Representation

/-!
# Simd Instruction Prefix

Reached SIMD states supply the source-bound acceptance premises for memory, scalar and bit-pattern callbacks. Those cases preserve the emitted instruction prefix.
-/

/-! ## SourceBoundSimdAcceptance -/

section

/-!
Complete SIMD reader replay from source bounds. Scalar, lane, bitwise and memory callback availability compose with the actual recorded source event.
-/

/-! ## Reader Simd Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Independent SIMD reader typing supplies all live operand and output-size
premises. Callback acceptance follows from allocation and source demand for
every nonconstant SIMD form, including lanes, memory and shuffle. Constants
use the separate checked pool-allocation callback theorem. -/
theorem reader_simd_nonconstant_available {data env locals index st source values position inputs output}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) (Body.Simd.inputTypes inputs) source
      (Body.Simd.outputTypes output))
    (post : Body.ReaderPost p out source p.current.ctrl.polymorphic_base values)
    (effect : Body.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Body.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (demand : CallbackDemand compiler out bound)
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    :
    runtime.compiler.lower.FunctionCompiler.op ops compiler out opcode a b bits ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  by_cases live : compiler.reachable = true
  · obtain ⟨front,types,oldTypes,concrete,newTypes⟩ := reader_simd_fixed_types post effect read (known live)
      (monomorphic live) capacity
    have layout := wholeLayout live
    have operandCapacity : compiler.before.length < Usize.max := by
      have same := layout.operands_length
      simp only [Body.Stack.stackTypes,List.length_map,alloc.vec.Vec.length] at same ⊢
      omega
    rw [oldTypes] at layout
    have outputLength : out.vals.val.length = (front ++ Body.Simd.outputTypes output).length := by
      have length := congrArg List.length newTypes
      simpa [concrete] using length
    exact compiler_simd_nonconstant_op_available ops bound available compiler out demand C front
      (Body.Simd.inputTypes inputs) (Body.Simd.outputTypes output) source opcode sub a b bits number
      meaning.opcode_bound meaning.not_constant meaning (fun _ => layout) (fun _ => outputLength)
      operandCapacity simdBound
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out opcode a b bits live
      demand.operands demand.slots)
    intro result held
    rw [held.2]
    exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Compiler

end

/-! ## Reached Simd Memory Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- The actual memory SIMD reader accepts from its independent source
memory rule and the retained live compiler layout, including dead code. -/
theorem reached_simd_memory_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (sub : U32) (next : Usize) (op : Body.Simd.MemoryOperation)
    (decoded : Binary.Leb128.Decoded data st.core.pos sub next)
    (meaning : Body.Simd.memoryMeaning sub.val = some op)
    (full : op.laneCount = 0)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨arg,middle,position,alignment,offset,checked,sourceCalled,read,controls,cursor,values,effect,post⟩ :=
    reader_simd_memory p recorder before after out ctx sub next op decoded meaning full byte reference
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_callback_meaning C sub op arg memory meaning full available
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset 0#u128)
      (Body.Simd.inputTypes (Body.Simd.fullMemoryInputs op.store))
      (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN 0))
      (Body.Simd.outputTypes (Body.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_full full,Body.Simd.MemoryOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_memory sub arg)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory compiler out.core sub arg ⦃ _ ⦄
    rw [compiler_simd_memory_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simd_compiler_opcode_val sub bounded) arg]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub arg.offset arg.align 0#u128 (simd_compiler_opcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.memory _ _ _ _ _ _ op meaning full] at raw ⊢
  exact recorded_reader_available (if op.store then code.read_store {st.core with pos := next} data env .V128 op.runtime.1
      else code.read_load {st.core with pos := next} data env .V128 op.runtime.1)
    (fun actual => .simd_memory sub actual) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_memory sub arg)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- The actual memory_lane SIMD reader accepts from its independent source
memory rule and the retained live compiler layout, including dead code. -/
theorem reached_simd_memory_lane_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (sub : U32) (next : Usize) (op : Body.Simd.MemoryOperation)
    (decoded : Binary.Leb128.Decoded data st.core.pos sub next)
    (meaning : Body.Simd.memoryMeaning sub.val = some op)
    (laned : op.laneCount ≠ 0)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨arg,middle,ending,lane,position,alignment,offset,span,laneBound,checked,sourceCalled,read,controls,cursor,values,effect,post⟩ :=
    reader_simd_memory_lane p recorder before after out ctx sub next op decoded meaning laned byte reference
  obtain ⟨memory,available⟩ := memory_reader_available env arg _ C contextMemories checked
  have retained := simd_memory_lane_callback_meaning C sub op arg lane memory meaning laned available
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub arg.offset (UScalar.cast .U128 lane))
      (Body.Simd.inputTypes [.V128,.I32]) (op.instruction (Body.MemoryMeaning.memArg arg) (.mk_uN lane.val))
      (Body.Simd.outputTypes (Body.Simd.memoryOutput op.store)) := by
    simpa only [op.inputs_lane laned,Body.Simd.MemoryOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_memory_lane sub arg lane)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_memory_lane compiler out.core sub arg lane ⦃ _ ⦄
    rw [compiler_simd_memory_lane_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simd_compiler_opcode_val sub bounded) arg lane]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub arg.offset arg.align (UScalar.cast .U128 lane) (simd_compiler_opcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.memory_lane _ _ _ _ _ _ op meaning laned] at raw ⊢
  exact recorded_reader_available (code.read_simd_memory_lane {st.core with pos := next} data env op.runtime.1 op.store op.runtime.2.2)
    (fun actual : code.MemArg × U8 => .simd_memory_lane sub actual.1 actual.2) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_memory_lane sub arg lane)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Itasca.Compiler

end

/-! ## Reached Simd Scalar Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- Replay the actual pure SIMD reader from its independently accepted
source event, with bounded real callback allocation and instruction charges. -/
theorem reached_simd_pure_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (sub : U32) (next : Usize) (op : Body.Simd.Operation)
    (decoded : Binary.Leb128.Decoded data st.core.pos sub next)
    (meaning : Body.Simd.pureMeaning sub.val = some op)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨sourceCalled,read,controls,position,values,effect,post⟩ := reader_simd_pure p
    recorder before after out ctx sub next op decoded meaning byte reference
  have bounded := Body.Simd.pure_bound meaning
  have retained : SimdImmediateMeaning C sub (simdImmediate sub 0#u32 0#u128)
      (Body.Simd.inputTypes op.signature.popTypes) op.instruction
      (Body.Simd.outputTypes (some op.signature.output)) := by
    simpa only [Body.Simd.Signature.inputs_pop,Body.Simd.Signature.outputs_pop] using
      (SimdImmediateMeaning.of_operation sub (simdImmediate sub 0#u32 0#u128) op meaning : SimdImmediateMeaning C _ _ _ _ _)
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd sub)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd compiler out.core sub ⦃ _ ⦄
    rw [compiler_simd_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded (simd_compiler_opcode_val sub bounded)]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub 0#u32 0#u32 0#u128 (simd_compiler_opcode_val sub bounded) retained post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.pure _ _ _ _ _ _ op meaning] at raw ⊢
  exact recorded_reader_available (code.read_simd_signature {st.core with pos := next} op.signature.runtime)
    (fun (_ : Unit) => .simd sub) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd sub)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- Replay the actual lane SIMD reader from its independently accepted
source event, with bounded real callback allocation and instruction charges. -/
theorem reached_simd_lane_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (sub : U32) (next : Usize) (op : Body.Simd.LaneOperation)
    (decoded : Binary.Leb128.Decoded data st.core.pos sub next)
    (meaning : Body.Simd.laneMeaning sub.val = some op)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after sub next decoded reference
  obtain ⟨lane,position,laneBound,span,sourceCalled,read,controls,cursor,values,effect,post⟩ := reader_simd_lane p
    recorder before after out ctx sub next op decoded meaning byte reference
  have retained := simd_lane_callback_meaning C sub op lane meaning
  have bounded := retained.opcode_bound
  have normalized : SimdImmediateMeaning C sub (simdImmediate sub (UScalar.cast .U32 lane) 0#u128)
      (Body.Simd.inputTypes (Body.Simd.laneInputs op.runtime.1 op.replace)) (op.instruction (.mk_uN lane.val))
      (Body.Simd.outputTypes (Body.Simd.laneOutput op.runtime.1 op.replace)) := by
    simpa only [Body.Simd.LaneOperation.inputs_pop,Body.Simd.LaneOperation.outputs_pop] using retained
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_lane sub lane)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_lane compiler out.core sub lane ⦃ _ ⦄
    rw [compiler_simd_lane_callback ops compiler out.core sub (simdCompilerOpcode sub) bounded
      (simd_compiler_opcode_val sub bounded) lane]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C (simdCompilerOpcode sub)
      sub (UScalar.cast .U32 lane) 0#u32 0#u128 (simd_compiler_opcode_val sub bounded) normalized post effect read capacity
      known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler sub next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.lane _ _ _ _ _ _ op meaning] at raw ⊢
  exact recorded_reader_available
    (code.read_simd_lane {st.core with pos := next} data op.runtime.1 op.runtime.2.1 op.replace)
    (fun actual => .simd_lane sub actual) (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
    before after out.core (.simd_lane sub lane)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Itasca.Compiler

end

/-! ## Reached Simd Bits Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace
set_option maxRecDepth 4096

/-- The actual sixteen-byte vector constant reader accepts under independently
bounded pool/observer demand, including dead code. -/
theorem reached_simd_constant_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (next : Usize)
    (decoded : Binary.Leb128.Decoded data st.core.pos 12#u32 next)
    (demand : CallbackDemand compiler out.core bound)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after 12#u32 next decoded reference
  obtain ⟨lo,hi,position,bits,sourceCalled,_⟩ := reader_simd_constant p recorder before after out ctx next decoded byte reference
  have callback := compiler_on_simd_const_available ops bound allocation compiler out.core demand lo hi poolBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler 12#u32 next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.constant] at raw ⊢
  exact recorded_reader_available (code.read_simd_const {st.core with pos := next} data)
    (fun actual : U64 × U64 => .simd_const actual.1 actual.2)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.simd_const lo hi)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

/-- Shuffle acceptance preserves its actual packed lane bytes and derives
live operand/output layouts from the independent fixed source effect. -/
theorem reached_simd_shuffle_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context) (next : Usize)
    (decoded : Binary.Leb128.Decoded data st.core.pos 13#u32 next)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,raw⟩ := simd_sub_success_of_decoded recorder st out data env ctx index before after 13#u32 next decoded reference
  obtain ⟨lo,hi,bits,bounds,sourceCalled,read,controls,values,effect,post⟩ := reader_simd_shuffle p
    recorder before after out ctx next decoded byte reference
  obtain ⟨sourceContext,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have physicalBase : (Body.Control.base {st.core with pos := next}).val = outer.length := by
    simp [Body.Control.base,ctrls,base]
  have fixed := simd_shuffle_fixed {st.core with pos := next} out.core data outer p.current.vals stack physicalBase
    capacity decoded.span.2.2 lo hi read
  have retained : SimdImmediateMeaning C 13#u32 (simdImmediate 13#u32 0#u32 (initializerBits lo hi))
      (Body.Simd.inputTypes [.V128,.V128]) (Body.Simd.shuffle lo hi) (Body.Simd.outputTypes (some .V128)) :=
    simd_shuffle_callback_meaning C lo hi
  have callback : invoke (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler
      (.op out.core (.simd_shuffle lo hi)) ⦃ result => result.1 = .Ok () ∧
        CompilationBudgetEffect compiler.budget result.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
    change (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_simd_shuffle compiler out.core lo hi ⦃ _ ⦄
    rw [compiler_simd_shuffle_callback ops compiler out.core lo hi]
    exact reader_simd_nonconstant_available p ops bound allocation compiler out.core C 525#u16
      13#u32 0#u32 0#u32 (initializerBits lo hi) rfl retained post effect fixed capacity known monomorphic wholeLayout demand simdBound
  apply simd_prefix_available (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st out data env ctx index
    compiler 13#u32 next (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) decoded capacity
  rw [Body.Simd.subStep.shuffle] at raw ⊢
  exact recorded_reader_available (code.read_simd_shuffle {st.core with pos := next} data)
    (fun actual : U64 × U64 => .simd_shuffle actual.1 actual.2)
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) compiler before after out.core (.simd_shuffle lo hi)
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) raw sourceCalled callback

end Itasca.Compiler

end

/-! ## Reached Simd Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Complete accepted SIMD dispatch: every pure, lane, memory, memory-lane,
constant, and shuffle form accepts with bounded actual compiler allocation.
The independent source dispatch excludes all unsupported subopcodes. -/
theorem reached_simd_available {data env locals index st}
    (p : Body.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map Translation.Environment.memType)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Body.Stack.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,sub,next,decoded,raw⟩ := simd_prefix_success recorder st out data env ctx index before after reference
  cases pure : Body.Simd.pureMeaning sub.val with
  | some op =>
    exact reached_simd_pure_available p ops bound allocation before after compiler out ctx C sub next op
      decoded pure demand known monomorphic wholeLayout simdBound byte reference
  | none =>
    cases lane : Body.Simd.laneMeaning sub.val with
    | some op =>
      exact reached_simd_lane_available p ops bound allocation before after compiler out ctx C sub next op
        decoded lane demand known monomorphic wholeLayout simdBound byte reference
    | none =>
      cases memory : Body.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · exact reached_simd_memory_available p ops bound allocation before after compiler out ctx C
            contextMemories sub next op decoded memory full demand known monomorphic wholeLayout simdBound byte reference
        · exact reached_simd_memory_lane_available p ops bound allocation before after compiler out ctx C
            contextMemories sub next op decoded memory full demand known monomorphic wholeLayout simdBound byte reference
      | none =>
        simp only [Body.Simd.subStep,Body.Simd.pure_table,pure,Body.Simd.lane_table,lane,
          Body.Simd.memory_table,memory,Option.map_none,bind_ok] at raw
        split at raw
        · exact reached_simd_constant_available p ops bound allocation before after compiler out ctx next
            decoded demand poolBound byte reference
        · exact reached_simd_shuffle_available p ops bound allocation before after compiler out ctx C next
            decoded demand known monomorphic wholeLayout simdBound byte reference
        · simp at raw

end Itasca.Compiler

end

/-! ## Source Simd Callback -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

private theorem reader_source_event {R : Type}
    (read : Result (core.result.Result R error.OpError × code.OpIterState)) (action : R → Action)
    (before after : List Observation) (out : code.OpIterState)
    (reference : Visitor.Core.run read (fun log state value => invoke recorder log (.op state (action value))) before =
      .ok (.Ok (),out,after)) :
    ∃ actual, invoke recorder before (.op out actual) = .ok (.Ok (),after) := by
  obtain ⟨value,_,called⟩ := Visitor.Core.run.accepted _ _ _ _ _ reference
  exact ⟨action value,called⟩

/-- Every successful SIMD reader ends in its actual recorded source event at
the final reader state. Unsupported subopcodes cannot supply this premise. -/
theorem source_simd_callback (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (before after : List Observation)
    (reference : code.step_profile recorder st data env ctx index 253#u8 before = .ok (.Ok (),out,after)) :
    ∃ action, invoke recorder before (.op out.core action) = .ok (.Ok (),after) := by
  obtain ⟨capacity,sub,next,decoded,raw⟩ := simd_prefix_success recorder st out data env ctx index before after reference
  cases pure : Body.Simd.pureMeaning sub.val with
  | some op =>
    rw [Body.Simd.subStep.pure _ _ _ _ _ _ op pure] at raw
    exact reader_source_event _ (fun (_ : Unit) => .simd sub) before after out.core raw
  | none =>
    cases lane : Body.Simd.laneMeaning sub.val with
    | some op =>
      rw [Body.Simd.subStep.lane _ _ _ _ _ _ op lane] at raw
      exact reader_source_event _ (fun lane => .simd_lane sub lane) before after out.core raw
    | none =>
      cases memory : Body.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · rw [Body.Simd.subStep.memory _ _ _ _ _ _ op memory full] at raw
          exact reader_source_event _ (fun arg => .simd_memory sub arg) before after out.core raw
        · rw [Body.Simd.subStep.memory_lane _ _ _ _ _ _ op memory full] at raw
          exact reader_source_event _ (fun arg : code.MemArg × U8 => .simd_memory_lane sub arg.1 arg.2)
            before after out.core raw
      | none =>
        simp only [Body.Simd.subStep,Body.Simd.pure_table,pure,Body.Simd.lane_table,lane,
          Body.Simd.memory_table,memory,Option.map_none,bind_ok] at raw
        split at raw
        · exact reader_source_event _ (fun bits : U64 × U64 => .simd_const bits.1 bits.2) before after out.core raw
        · exact reader_source_event _ (fun bits : U64 × U64 => .simd_shuffle bits.1 bits.2) before after out.core raw
        · simp at raw

end Itasca.Compiler

end

/-! ## Source Bound Simd Acceptance -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace

/-- Source typing, source byte room, and the independent final reference
log construct all demands for actual complete SIMD reader acceptance. -/
theorem IndexedTableReaderCompilerPoint.simd_available_from_source {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns localTypes data env sourceLocals index ft st}
    (point : IndexedTableReaderCompilerPoint emit initial compiler types functions returns localTypes
      data env sourceLocals index ft st)
    (C : context) (matched : Translation.Environment.Matches env ⟨sourceLocals,ft.results⟩ C)
    (ledger : ReachedCompilerLedger compiler st.core.vals.val)
    (before after final : List Observation) (out : code.BodyState)
    (room : BodyResourceRoom initial data.length (observationDemand final).operands bound)
    (budget : SourceCompilationBudget initial.budget compiler.budget bodyResourceRate st.core.pos.val)
    (nonempty : st.core.ctrls.val ≠ []) (next : Usize)
    (advance : next.val = st.core.pos.val+1) (inbounds : st.core.pos.val<data.length)
    (byte : data.val[st.core.pos.val] = 253#u8)
    (reference : code.step_profile recorder {core := {st.core with pos := next}} data env
      ⟨sourceLocals,ft.results⟩ index data.val[st.core.pos.val] before = .ok (.Ok (),out,after))
    (suffix : code.body_loop_loop recorder data env ⟨sourceLocals,ft.results⟩ index before st =
      .ok (.Ok (),final)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ⟨sourceLocals,ft.results⟩ index
      data.val[st.core.pos.val] compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let pending := state.boundary.pending next advance inbounds
  have tail := code.body_loop_loop.accepted_tail recorder data env ⟨sourceLocals,ft.results⟩ index st out
    before after final nonempty inbounds next advance reference suffix
  have canonical := reference
  rw [byte] at canonical
  obtain ⟨action,callback⟩ := source_simd_callback _ out data env ⟨sourceLocals,ft.results⟩ index before after canonical
  have operands := (source_callback_demand before after final out.core action (.Ok ()) out data env
    ⟨sourceLocals,ft.results⟩ index (.Ok ()) callback tail).1
  have demand := room.demand budget state.compiled.metadata state.compiled.codeBudget state.compiled.sources
    state.compiled.cursor inbounds out.core operands
  rw [byte]
  exact reached_simd_available pending ops bound allocation before after compiler out
    ⟨sourceLocals,ft.results⟩ C matched.mems demand state.compiled.known state.reach.current
    (fun live => (state.compiled.live live).2.layout) ledger.simd ledger.constants byte canonical

end Itasca.Compiler

end

end

/-! ## SimdInstructionPrefix -/

section

/-!
The exhaustive actual SIMD event classifier supplies source widths and exact metadata appends. Every live form checks its new instruction; dead forms only observe. Both retain the slot regions of earlier forward exits.

Main declarations: `SimdReaderEvent.instruction_prefix`.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- The exhaustive actual SIMD event classifier supplies source widths and
exact metadata appends. Every live form checks its new instruction; dead forms
only observe. Both retain the slot regions of earlier forward exits. -/
theorem SimdReaderEvent.instruction_prefix {jumpTables : List U32} {A : Type} {ops : runtime.platform.Alloc A}
    {data env sourceLocals index st p initial before after out C}
    (event : @SimdReaderEvent A ops data env sourceLocals index st p before after out C)
    (law : Platform.AllocCorrect ops)
    {emit types functions returns locals parents current}
    (contextLocals : C.LOCALS = locals)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val+data.length ≤ Usize.max)
    (held : CompilerInstructionPrefix before) (exits : FrameExitSlotBounds before) :
    CompilerInstructionPrefix after ∧ FrameExitSlotBounds after := by
  cases reachable : before.reachable with
  | false =>
    have checked := compiler_dead_op_open_instructions ops law before after out event.opcode event.a event.b event.bits
      reachable held event.callback
    have observed := event.callback
    rw [runtime.compiler.lower.FunctionCompiler.op.dead _ _ _ _ _ _ _ (reachable)] at observed
    exact ⟨checked,compiler_observe_exit_slots ops law before after out exits observed⟩
  | true =>
    obtain ⟨entered,retained⟩ := invariant.live reachable
    have bound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := (Nat.le_of_lt p.inbounds).trans sourceBound
    obtain ⟨codeFits,sourceFits,_,_⟩ := invariant.capacities bound
    have coordinateFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by
      have cursor := invariant.cursor
      have position := p.inbounds
      omega
    obtain ⟨ordinary,sources,cursor,extra,front,emitted,tables,oldTypes,lowered,emission⟩ :=
      reader_simd_callback_emission p ops law before after out C event.opcode event.sub event.a event.b event.bits event.number
        event.meaning event.post event.effect event.read (invariant.known reachable) (monomorphic reachable) event.capacity
        (contextLocals.trans retained.localsEq.symm) retained.layout reachable codeFits sourceFits coordinateFits event.callback
    have growth := instruction_check_extends_of_tables_append before.function after.function extra tables
      ordinary.capacity (by change before.function.code.val.length ≤ after.function.code.val.length; rw [lowered.1.1,List.length_append,List.length_singleton]; omega)
    have layout := retained.layout
    rw [oldTypes] at layout
    exact ⟨lowered.1.executable_instruction_prefix layout reachable (contextLocals.trans retained.localsEq.symm)
      (.simd emission) emission.not_branch_table growth held ordinary.frames,
      exits.retained (congrArg alloc.vec.Vec.val ordinary.frames) ordinary.capacity⟩

end Itasca.Compiler

end

end

/-! ## SingleCallbackSimd -/

section

/-!
# Single callbacks for SIMD steps

Independent SIMD tables bound selected subopcodes. Every accepted SIMD substep invokes exactly one of the six SIMD event forms, supporting callback replay.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Visitor.Trace Itasca.Body.Simd
set_option maxRecDepth 4096

private theorem pure_meaning_bound {opcode : Nat} {op : Operation}
    (found : pureMeaning opcode = some op) : opcode < 256 := by
  by_cases beyond : opcode ≥ 256
  · unfold pureMeaning at found
    rw [if_pos beyond] at found
    cases found
  · exact Nat.lt_of_not_ge beyond

private theorem lane_meaning_bound {opcode : Nat} {op : LaneOperation}
    (found : laneMeaning opcode = some op) : opcode < 256 := by
  unfold laneMeaning at found
  split at found <;> simp_all <;> omega

private theorem memory_meaning_bound {opcode : Nat} {op : MemoryOperation}
    (found : memoryMeaning opcode = some op) : opcode < 256 := by
  unfold memoryMeaning at found
  split at found <;> simp_all <;> omega

/-- The independent SIMD tables bound every selected subopcode and every
accepted substep calls exactly one of the six SIMD visitor event forms. -/
theorem reader_single_callback_simd_sub {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env) (opcode : U32)
    (before after : V) (out : code.OpIterState)
    (accepted : subStep visitor st data env opcode before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  unfold subStep at accepted
  rw [pure_table] at accepted
  cases hp : pureMeaning opcode.val with
  | some op =>
    simp only [hp,Option.map_some,bind_ok] at accepted
    exact reader_single_callback_of_run visitor _ (fun _ _ => .simd opcode) before after out
      (by intro arg; exact ⟨True.intro,pure_meaning_bound hp⟩) accepted
  | none =>
    simp only [hp,Option.map_none,bind_ok] at accepted
    rw [lane_table] at accepted
    cases hl : laneMeaning opcode.val with
    | some lane =>
      simp only [hl,Option.map_some,bind_ok] at accepted
      rcases runtime : lane.runtime with ⟨ty,count,replace⟩
      simp only [runtime] at accepted
      exact reader_single_callback_of_run visitor _ (fun _ arg => .simd_lane opcode arg) before after out
        (by intro arg; exact ⟨True.intro,lane_meaning_bound hl⟩) accepted
    | none =>
      simp only [hl,Option.map_none,bind_ok] at accepted
      rw [memory_table] at accepted
      cases hm : memoryMeaning opcode.val with
      | some mem =>
        simp only [hm,Option.map_some,bind_ok] at accepted
        rcases runtime : mem.runtime with ⟨alignment,store,count⟩
        simp only [runtime] at accepted
        split at accepted
        · exact reader_single_callback_of_run visitor _
            (fun _ (arg : code.MemArg × U8) => .simd_memory_lane opcode arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,memory_meaning_bound hm⟩) accepted
        · cases store <;> simp only [Bool.false_eq_true,if_true,if_false] at accepted
          all_goals
            exact reader_single_callback_of_run visitor _ (fun _ arg => .simd_memory opcode arg) before after out
              (by intro arg; exact ⟨True.intro,memory_meaning_bound hm⟩) accepted
      | none =>
        simp only [hm,Option.map_none,bind_ok] at accepted
        split at accepted
        · exact reader_single_callback_of_run visitor _ (fun _ (arg : U64 × U64) => .simd_const arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
        · exact reader_single_callback_of_run visitor _ (fun _ (arg : U64 × U64) => .simd_shuffle arg.1 arg.2) before after out
            (by intro arg; exact ⟨True.intro,True.intro⟩) accepted
        · simp at accepted

/-- SIMD prefix decoding retains the exact event and its independently bounded
subopcode; it does not introduce an additional callback. -/
theorem reader_single_callback_simd {V : Type} (visitor : code.OpVisitor V)
    (st : code.OpIterState) (data : Slice U8) (env : metadata.Env)
    (before after : V) (out : code.OpIterState)
    (accepted : code.step_simd visitor st data env before = .ok (.Ok (),out,after)) :
    ∃ action, NoScopeBoundary action ∧ PublicationActionRange action ∧
      invoke visitor before (.op out action) = .ok (.Ok (),after) := by
  rw [code.step_simd.eq_runs] at accepted
  unfold prefixStep at accepted
  obtain ⟨read,called⟩ := reader.read_u32_leb.total data st.pos
  simp only [called,bind_ok] at accepted
  cases read with
  | Err error => simp at accepted
  | Ok pair =>
    obtain ⟨opcode,next⟩ := pair
    exact reader_single_callback_simd_sub visitor _ data env opcode before after out accepted

end Itasca.Compiler

end
