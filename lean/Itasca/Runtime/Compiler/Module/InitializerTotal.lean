import Itasca.Runtime.Compiler.Module.InitializerTotalBasic
import Itasca.Runtime.Compiler.Module.InitializerTotalMappings

/-!
Normal return of initializer emission and segment loops, composed into complete initializer lowering.
-/

/-! ## Initializer Total Emit -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[step] theorem initializer_emit_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (code : alloc.vec.Vec runtime.bytecode.Instr) (instruction : runtime.bytecode.Instr)
    (space : code.val.length < Usize.max) :
    runtime.compiler.initialize.emit ops budget code instruction ⦃ out =>
      out.2.2.val.length ≤ code.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit
  step with charge_instruction ops budget as ⟨status, nextBudget, _⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    exact initializer_push_total ops law nextBudget code instruction space

/-- All constant forms return normally, including an allocator or instruction
budget rejection after partial emission. Each vector grows by at most one. -/
@[step] theorem initializer_constant_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (function : runtime.bytecode.CompiledFunction) (expr : Itasca.types.ConstExpr)
    (ty : Itasca.types.ValueType) (dst : U32)
    (codeFits : function.code.val.length < Usize.max)
    (poolFits : function.v128_pool.val.length < Usize.max) :
    runtime.compiler.initialize.constant ops budget function expr ty dst ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 1 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  cases expr <;> unfold runtime.compiler.initialize.constant
  all_goals repeat' first
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | omega

/-- A single segment emits at most five instructions, one vector constant,
and one table-index pair. The bounds include rejected partial emissions. -/
@[step] theorem initializer_emit_element_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.env.elements.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max)
    (pairFits : function.indirect.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_element ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + 1 ⦄ := by
  unfold runtime.compiler.initialize.emit_element
  simp only [runtime.compiler.ExecutableModule.env,
    Itasca.module.Module.impl.env, Itasca.module.Env.impl.elements, bind_ok]
  step
  · simpa [alloc.vec.Vec.deref] using bound
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | (step with initializer_push_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac

@[step] theorem initializer_emit_data_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (codeFits : function.code.val.length + 5 ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + 1 ≤ Usize.max) :
    runtime.compiler.initialize.emit_data ops m budget function index ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + 1 ∧
      out.2.2.indirect = function.indirect ⦄ := by
  unfold runtime.compiler.initialize.emit_data
  simp only [runtime.compiler.ExecutableModule.tail,
    Itasca.module.Module.impl.tail, bind_ok]
  step
  repeat' first
    | (step with initializer_constant_total ops law _ _ _ _ _ (by scalar_tac) (by scalar_tac))
    | (step with initializer_emit_total ops law _ _ _ (by scalar_tac))
    | simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, WP.spec_ok]
    | split
    | step
    | (apply And.intro)
    | assumption
    | rfl
    | scalar_tac
end Itasca.Runtime.Code

end

/-! ## Initializer Total Segments -/

section

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

end

/-! ## Initializer Total -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

/-- A source-derived upper bound on all retained initializer-map appends. -/
def initializerMappingCost (source : Itasca.module.Module) : Nat :=
  2 * source.env.globals.val.length + initializerElementCost source.env.elements.val +
  2 * source.tail.data.val.length

/-- Initializer lowering returns normally under its finite append headroom.
These quantitative input bounds concern internal vectors, not correctness of
compiled code or normal return of a subcomputation. Every allocator refusal,
instruction-budget rejection, and checker rejection is included. -/
@[step] theorem initializer_lower_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (mapSpace : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + initializerMappingCost m.module + 1 ⦄ := by
  let seed := { initializerSeed .I32 with slot_count := 0#u32 }
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  unfold runtime.compiler.initialize.lower
  step with initializer_mapping_loop0_total ops law m budget 0#usize (.Ok ())
    (by simp only [initializerMappingCost] at mapSpace; simp; omega)
    as ⟨m1, b1, status, source1, size1⟩
  simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero] at size1
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, source1]
    unfold initializerMappingCost; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_mapping_loop1_total ops law m1 b1 0#usize (.Ok value)
      (by simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1]; unfold initializerMappingCost at mapSpace; omega)
      as ⟨m2, b2, status, source2, size2⟩
    have same2 : m2.module = m.module := source2.trans source1
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1] at size2
    cases status with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same2]
      unfold initializerMappingCost; omega
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with initializer_mapping_loop2_total ops law m2 b2 0#usize (.Ok value)
        (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2]; unfold initializerMappingCost at mapSpace; omega)
        as ⟨m3, b3, status, source3, size3⟩
      have same3 : m3.module = m.module := source3.trans same2
      simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2] at size3
      have sizeBound : initializerSize m3 ≤ initializerSize m + initializerMappingCost m.module := by
        unfold initializerMappingCost; omega
      cases status with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
        omega
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        rw [seedEq, bind_ok]
        step with initializer_segment_loop3_total ops law m3 b3 seed 0#usize (.Ok value)
          (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega)
          as ⟨b4, status, function1, code1, pool1, pairs1⟩
        simp [seed, initializerSeed, same3] at code1 pool1 pairs1
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
          omega
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_segment_loop4_total ops law m3 b4 function1 0#usize (.Ok value)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            as ⟨b5, status, function2, code2, pool2, pairs2⟩
          simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3] at code2
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
            omega
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with initializer_emit_total ops law b5 function2.code _ (by omega)
              as ⟨status, b6, finalCode, codeCount⟩
            cases status with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
              omega
            | Ok value =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step with well_formed_total { function2 with code := finalCode } as ⟨valid⟩
              cases valid with
              | false => simp [same3]; omega
              | true =>
                simp only [↓reduceIte]
                step with initializer_push_total ops law b6 m3.functions _
                  (by unfold initializerSize at sizeBound mapSpace; omega)
                  as ⟨status, b7, functions, count⟩
                exact ⟨same3, by unfold initializerSize at *; dsimp at *; omega⟩

/-- Driver-facing form: initializer maps are freshly empty, so only source
counts and the already compiled function count consume the retained allowance. -/
theorem initializer_lower_fresh_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (globals : m.global_initializers.val = [])
    (elements : m.element_initializers.val = [])
    (elementOffsets : m.element_offsets.val = [])
    (dataOffsets : m.data_offsets.val = [])
    (mapSpace : m.functions.val.length + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ _ => True ⦄ := by
  have headroom : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max := by
    simpa [initializerSize, globals, elements, elementOffsets, dataOffsets] using mapSpace
  apply WP.spec_mono (initializer_lower_total ops law m budget headroom segmentSpace)
  intros; trivial

end Itasca.Runtime.Code

end
