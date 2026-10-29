import Itasca.Runtime.Compiler.Body.Reader.Safety.Run
import Itasca.Runtime.Compiler.Body.Relations.Calls.OrdinaryCallbackReady
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdSafetyCallbacks
import Itasca.Wasm2.Simd.DispatchTotal

/-!
Normal return of SIMD subopcode and top-level reader dispatch.

Main declarations: `compiler_reader_simd_sub_total` and `compiler_reader_simd_total`. A direct consumer is `Compiler.Body.Reader.Safety.OrdinarySafety`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.Wasm2.Simd

theorem compiler_reader_simd_sub_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (sub : U32)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    subStep (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env sub compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  unfold subStep
  rw [pure_table]
  cases meaning : pureMeaning sub.val with
  | some op =>
    simp only [Option.map_some,bind_ok]
    refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
    · exact WP.spec_mono (signature_total _ _ shape capacity) (by simp)
    · intro state value read
      exact compiler_on_simd_total ops law compiler state sub (pure_bound meaning)
        ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
  | none =>
    simp only [Option.map_none,bind_ok]
    rw [lane_table]
    cases laneMeaningEq : laneMeaning sub.val with
    | some lane =>
      have bound : sub.val < 256 := by
        unfold laneMeaning at laneMeaningEq
        split at laneMeaningEq <;> first | contradiction | omega
      simp only [Option.map_some,bind_ok]
      rcases runtimeEq : lane.runtime with ⟨ty,count,replace⟩
      simp only
      refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
      · exact WP.spec_mono (read_lane_total _ _ _ _ _ shape capacity) (by simp)
      · intro state value read
        exact compiler_on_simd_lane_total ops law compiler state sub value bound
          ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
    | none =>
      simp only [Option.map_none,bind_ok]
      rw [memory_table]
      cases memoryMeaningEq : memoryMeaning sub.val with
      | some mem =>
        have bound : sub.val < 256 := by
          unfold memoryMeaning at memoryMeaningEq
          split at memoryMeaningEq <;> first | contradiction | omega
        simp only [Option.map_some,bind_ok]
        rcases runtimeEq : mem.runtime with ⟨align,store,count⟩
        simp only
        split
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (memory_lane_total _ _ _ _ _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_memory_lane_total ops law compiler state sub value.1 value.2 bound
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · split
          · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
            · exact WP.spec_mono (store_total _ _ _ _ _ shape) (by simp)
            · intro state value read
              exact compiler_on_simd_memory_total ops law compiler state sub value bound
                ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
          · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
            · exact WP.spec_mono (load_total _ _ _ _ _ shape capacity) (by simp)
            · intro state value read
              exact compiler_on_simd_memory_total ops law compiler state sub value bound
                ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
      | none =>
        simp only [Option.map_none,bind_ok]
        split
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (constant_total _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_const_total ops law compiler state value.1 value.2
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · refine reader_run_reached _ _ _ (fun state after => ObservedStack after state.vals.val) ?_ ?_
          · exact WP.spec_mono (shuffle_total _ _ shape capacity) (by simp)
          · intro state value read
            exact compiler_on_simd_shuffle_total ops law compiler state value.1 value.2
              ready.codeFits ready.sourceFits ready.coordinateFits ready.poolFits ready.simdFits
        · simp

/-- The actual SIMD prefix handles malformed subopcode LEBs and all six
callback families, with no accepted-reader or compiler-success premise. -/
theorem compiler_reader_simd_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (st : code.OpIterState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (ready : OrdinaryCallbackReady compiler env ctx st.vals.val)
    (shape : Control.Shape st) (capacity : st.vals.val.length < Usize.max) :
    code.step_simd (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env compiler ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2.2 out.2.1.vals.val ⦄ := by
  rw [code.step_simd.eq_runs]
  unfold prefixStep
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.pos)
  rw [read]
  simp only [bind_ok]
  cases result with
  | Err error => simp
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    exact compiler_reader_simd_sub_total ops law compiler {st with pos := next} data env ctx sub
      ready ⟨shape.ordered,shape.bounded⟩ capacity
end Itasca.Runtime.Compiler
