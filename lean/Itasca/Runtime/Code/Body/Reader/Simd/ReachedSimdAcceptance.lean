import Itasca.Runtime.Code.Body.Reader.Simd.ReachedSimdScalarAcceptance
import Itasca.Runtime.Code.Body.Reader.Simd.ReachedSimdMemoryAcceptance
import Itasca.Runtime.Code.Body.Reader.Simd.ReachedSimdBitsAcceptance

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Complete accepted SIMD dispatch: every pure, lane, memory, memory-lane,
constant, and shuffle form accepts with bounded actual compiler allocation.
The independent source dispatch excludes all unsupported subopcodes. -/
theorem reached_profile_simd_available_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (before after : List Observation) (compiler : runtime.compiler.FunctionCompiler A)
    (out : code.BodyState) (ctx : code.Context) (C : context)
    (contextMemories : C.MEMS = env.mem_types.val.map EnvTranslation.memType)
    (demand : CallbackDemand compiler out.core bound)
    (known : compiler.reachable = true → ConcreteStack st.core.vals.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (wholeLayout : compiler.reachable = true → CompilerLayout compiler (Sequence.stackTypes st.core.vals.val))
    (simdBound : compiler.function.simd.length ≤ compiler.function.code.length)
    (poolBound : compiler.function.v128_pool.length ≤ compiler.function.code.length)
    (byte : data.val[p.start.val]'p.inbounds = 253#u8)
    (reference : code.step_profile recorder st data env ctx index .Wasm2 253#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 253#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨capacity,sub,next,decoded,raw⟩ := simd_prefix_success recorder st out data env ctx index before after reference
  cases pure : Wasm2.Simd.pureMeaning sub.val with
  | some op =>
    exact reached_profile_simd_pure_available_wasm2 p ops bound allocation before after compiler out ctx C sub next op
      decoded pure demand known monomorphic wholeLayout simdBound byte reference
  | none =>
    cases lane : Wasm2.Simd.laneMeaning sub.val with
    | some op =>
      exact reached_profile_simd_lane_available_wasm2 p ops bound allocation before after compiler out ctx C sub next op
        decoded lane demand known monomorphic wholeLayout simdBound byte reference
    | none =>
      cases memory : Wasm2.Simd.memoryMeaning sub.val with
      | some op =>
        by_cases full : op.laneCount = 0
        · exact reached_profile_simd_memory_available_wasm2 p ops bound allocation before after compiler out ctx C
            contextMemories sub next op decoded memory full demand known monomorphic wholeLayout simdBound byte reference
        · exact reached_profile_simd_memory_lane_available_wasm2 p ops bound allocation before after compiler out ctx C
            contextMemories sub next op decoded memory full demand known monomorphic wholeLayout simdBound byte reference
      | none =>
        simp only [Wasm2.Simd.subStep,Wasm2.Simd.pure_table,pure,Wasm2.Simd.lane_table,lane,
          Wasm2.Simd.memory_table,memory,Option.map_none,bind_ok] at raw
        split at raw
        · exact reached_profile_simd_constant_available_wasm2 p ops bound allocation before after compiler out ctx next
            decoded demand poolBound byte reference
        · exact reached_profile_simd_shuffle_available_wasm2 p ops bound allocation before after compiler out ctx C next
            decoded demand known monomorphic wholeLayout simdBound byte reference
        · simp at raw

end Itasca.Runtime.Code
