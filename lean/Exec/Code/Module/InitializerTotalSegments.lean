import Exec.Code.Module.InitializerTotalEmit
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000

@[step] theorem initializer_segment_loop3_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (pairFits : function.indirect.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop3 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + (m.module.env.elements.val.length - i.val) ⦄ := by
  unfold runtime.compiler.initialize.lower_loop3
  apply loop.spec_decr_nat (fun st => m.module.env.elements.val.length - st.2.1.val)
    (fun st => st.2.2.2.code.val.length + 5 * (m.module.env.elements.val.length - st.2.1.val) ≤
        function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ∧
      st.2.2.2.v128_pool.val.length + (m.module.env.elements.val.length - st.2.1.val) ≤
        function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ∧
      st.2.2.2.indirect.val.length + (m.module.env.elements.val.length - st.2.1.val) ≤ function.indirect.val.length + (m.module.env.elements.val.length - i.val))
  · rintro ⟨b, index, result, current⟩ ⟨code, pool, pairs⟩
    unfold runtime.compiler.initialize.lower_loop3.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.env,
      Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < m.module.env.elements.val.length := by
        simpa [UScalar.lt_equiv, Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] using more
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨by omega, by omega, by omega⟩
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_emit_element_total ops law m b current index inbounds
          (by omega) (by omega) (by omega) as ⟨status, b1, next, codeGrowth, poolGrowth, pairGrowth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · scalar_tac
        · scalar_tac
        · scalar_tac
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨by omega, by omega, by omega⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

@[step] theorem initializer_segment_loop4_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop4 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ∧
      out.2.2.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.lower_loop4
  apply loop.spec_decr_nat (fun st => m.module.tail.data.val.length - st.2.1.val)
    (fun st => st.2.2.2.code.val.length + 5 * (m.module.tail.data.val.length - st.2.1.val) ≤
        function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ∧
      st.2.2.2.v128_pool.val.length + (m.module.tail.data.val.length - st.2.1.val) ≤
        function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ∧
      st.2.2.2.indirect = function.indirect)
  · rintro ⟨b, index, result, current⟩ ⟨code, pool, pairs⟩
    unfold runtime.compiler.initialize.lower_loop4.body
    dsimp only at *
    simp only [runtime.compiler.ExecutableModule.tail,
      Itasca.module.Module.impl.tail, bind_ok]
    split
    · rename_i more
      have inbounds : index.val < m.module.tail.data.val.length := by scalar_tac
      cases result with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨by omega, by omega, pairs⟩
      | Ok value =>
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with initializer_emit_data_total ops law m b current index inbounds
          (by omega) (by omega)  as ⟨status, b1, next, codeGrowth, poolGrowth, pairGrowth⟩
        step as ⟨nextIndex, increment⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · scalar_tac
        · scalar_tac
        · exact pairGrowth.trans pairs
        · scalar_tac
    · simp only [WP.spec_ok]
      exact ⟨by omega, by omega, pairs⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
end Itasca.Runtime.Code
