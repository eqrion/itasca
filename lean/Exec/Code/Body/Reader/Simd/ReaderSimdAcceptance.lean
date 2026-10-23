import Exec.Code.Body.Lowering.Simd.SimdCallbackMeaning
import Exec.Code.Body.Reader.Simd.ReaderSimdTypes
import Exec.Code.Local.Capacity.SimdOpAvailability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Independent SIMD reader typing supplies all live operand and output-size
premises. Callback acceptance follows from allocation and source demand for
every nonconstant SIMD form, including lanes, memory and shuffle. Constants
use the separate checked pool-allocation callback theorem. -/
theorem reader_simd_nonconstant_available {data env locals index st source values position inputs output}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (C : context) (opcode : U16) (sub a b : U32) (bits : U128)
    (number : opcode.val = 512+sub.val)
    (meaning : SimdImmediateMeaning C sub (simdImmediate sub a bits) (Wasm2.Simd.inputTypes inputs) source
      (Wasm2.Simd.outputTypes output))
    (post : ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values)
    (effect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out))
    (capacity : st.core.vals.val.length < Usize.max)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
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
      simp only [Sequence.stackTypes,List.length_map,alloc.vec.Vec.length] at same ⊢
      omega
    rw [oldTypes] at layout
    have outputLength : out.vals.val.length = (front ++ Wasm2.Simd.outputTypes output).length := by
      have length := congrArg List.length newTypes
      simpa [concrete] using length
    exact compiler_simd_nonconstant_op_available ops bound available compiler out demand C front
      (Wasm2.Simd.inputTypes inputs) (Wasm2.Simd.outputTypes output) source opcode sub a b bits number
      meaning.opcode_bound meaning.not_constant meaning (fun _ => layout) (fun _ => outputLength)
      operandCapacity simdBound
  · apply WP.spec_mono (compiler_dead_op_available ops bound available compiler out opcode a b bits live
      demand.operands demand.slots)
    intro result held
    rw [held.2]
    exact ⟨held.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩


end Exec.Code
