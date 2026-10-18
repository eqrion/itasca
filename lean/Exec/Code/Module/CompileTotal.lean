import Exec.Code.Module.PreparedExecutableSafety
import Exec.Code.Body.Relations.Common.ReachedBodySafetyWasm2
import Exec.Code.Body.Reader.Common.ReaderBodyTooLarge
import Exec.Code.Body.Relations.Common.ReachedBodyWasm1
import Exec.Code.Module.CompileDefaultTotal
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- Every Wasm 2 body reached by the actual compiler returns normally. The
initial source and allocation invariants come from actual entry setup. -/
theorem profile_prepared_bodies_total_wasm2 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ProfilePreparedBodiesTotal ops .Wasm2 := by
  intro data env index start signatures functionSlots budget batchStart initial started prepared
    bounds environment signaturesMatch slotsMatch batchBound created begun
  by_cases small : prepared.body.length ≤ limits.MAX_FUNCTION_BYTES.val
  · obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety_wasm2 ops law prepared small signaturesMatch slotsMatch batchBound created begun
    have contextEq : prepared.ctx = ⟨prepared.ctx.locals,prepared.ft.results⟩ := by
      have results : prepared.ctx.results = prepared.ft.results :=
        alloc.vec.Vec.ext _ _ prepared.context_results
      cases h : prepared.ctx
      simp_all
    have body := compiler_body_wasm2_total ops law started (EnvTranslation.context env prepared.ctx)
      (prepared.ctx.locals.val.map Translate.valueType) prepared.body env prepared.ctx.locals prepared.typeIdx prepared.ft
      point facts.localLayout facts.locals facts.functionSlots matched rfl facts.signatures
      ⟨observed,indirect,simd,pool,fixups⟩ facts.bodyBound
    change code.validate_body_with_profile _ prepared.body env prepared.ctx prepared.typeIdx .Wasm2 started ⦃ _ => True ⦄
    rw [contextEq]
    exact body
  · rw [reader_body_too_large _ .Wasm2 prepared.body env prepared.ctx prepared.typeIdx started (by omega)]
    simp

/-- Every Wasm 1 body reached by the actual compiler returns normally. Its
single-result restriction follows from successful environment validation. -/
theorem profile_prepared_bodies_total_wasm1 {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) : ProfilePreparedBodiesTotal ops .Wasm1 := by
  intro data env index start signatures functionSlots budget batchStart initial started prepared
    bounds environment signaturesMatch slotsMatch batchBound created begun
  by_cases small : prepared.body.length ≤ limits.MAX_FUNCTION_BYTES.val
  · obtain ⟨facts,matched,results,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety_wasm1 ops law prepared small environment signaturesMatch slotsMatch batchBound created begun
    exact compiler_body_wasm1_total ops law started prepared.body env prepared.ctx
      (EnvTranslation.context env prepared.ctx) point facts.localLayout facts.locals facts.functionSlots
      matched rfl facts.signatures results facts.bodyBound ⟨observed,indirect,simd,pool,fixups⟩
  · rw [reader_body_too_large _ .Wasm1 prepared.body env prepared.ctx prepared.typeIdx started (by omega)]
    simp

/-- Actual prepared function bodies return normally for either supported
profile, without a body-acceptance or callback-correctness premise. -/
theorem profile_prepared_bodies_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile) :
    ProfilePreparedBodiesTotal ops profile := by
  cases profile with
  | Wasm1 => exact profile_prepared_bodies_total_wasm1 ops law
  | Wasm2 => exact profile_prepared_bodies_total_wasm2 ops law

/-- Complete-module compilation returns success or a reported validation or
resource error on arbitrary bytes and arbitrary compiler limits. -/
@[step] theorem compile_with_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ :=
  compile_with_total_of_profile_prepared_bodies ops law bytes profile limits
    (profile_prepared_bodies_total ops law profile)

/-- The default-limit compiler has the same normal-return guarantee; resource
errors are converted by its actual public error-mapping branch. -/
@[step] theorem compile_default_with_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile) :
    runtime.compiler.compile_default_with ops bytes profile ⦃ _ => True ⦄ := by
  unfold runtime.compiler.compile_default_with
  step with compiler_default_limits_total as ⟨limits⟩
  step with compile_with_total ops law bytes profile limits as ⟨result⟩
  cases result with
  | Ok executable => simp
  | Err error => cases error <;> simp
end Exec.Code
