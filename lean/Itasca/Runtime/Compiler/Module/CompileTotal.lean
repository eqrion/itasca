import Itasca.Runtime.Compiler.Module.PreparedExecutableSafety
import Itasca.Runtime.Compiler.Body.Relations.Replay.ReachedBodySafetyWasm2
import Itasca.Runtime.Compiler.Body.Reader.Replay.BodyTooLarge
import Itasca.Runtime.Compiler.Module.CompileProfileTotal
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual prepared function bodies return normally for the supported profile,
without a body-acceptance or callback-correctness premise. The initial source
and allocation invariants come from actual entry setup. -/
theorem profile_prepared_bodies_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (profile : ValidationProfile) :
    ProfilePreparedBodiesTotal ops profile := by
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
    rw [← contextEq] at body
    obtain ⟨result,run,_⟩ := WP.spec_imp_exists body
    cases profile with
    | Wasm2 => simp [run]
  · rw [reader_body_too_large _ profile prepared.body env prepared.ctx prepared.typeIdx started (by omega)]
    simp

/-- Complete-module compilation returns success or a reported validation or
resource error on arbitrary bytes and arbitrary compiler limits. -/
@[step] theorem compile_with_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits) :
    runtime.compiler.compile_with ops bytes profile limits ⦃ _ => True ⦄ :=
  compile_with_total_of_profile_prepared_bodies ops law bytes profile limits
    (profile_prepared_bodies_total ops law profile)

end Itasca.Runtime.Compiler
