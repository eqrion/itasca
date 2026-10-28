import Itasca.Runtime.Code.Module.InitializerTotalMappings
import Itasca.Runtime.Code.Module.InitializerTotalSegments
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
