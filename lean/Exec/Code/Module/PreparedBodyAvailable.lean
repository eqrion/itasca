import Exec.Code.Module.PreparedExecutableSafety
import Exec.Code.Body.Relations.Common.BodyAcceptanceWasm1
import Exec.Code.Body.Relations.Common.BodyAcceptanceWasm2

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual entry preparation supplies the initial executable prefix for either
profile. Independent body validity and numerical room then suffice for body
acceptance; the resulting budget is bounded by source bytes. -/
theorem prepared_body_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (environment : Profile.Environment profile env) (limits : Profile.EnvironmentWithinLimits profile env)
    (body : Profile.Body profile w.body env w.ctx.locals w.typeIdx)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (room : BodyResourceRoom started w.body.length
      (independentBodyDemand profile w.body env w.ctx w.typeIdx).operands bound) :
    CodeEntry.runBody (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) profile w.body env
      w.ctx w.typeIdx started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  cases profile with
  | Wasm1 =>
    obtain ⟨facts,matched,results,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety_wasm1 ops law w room.size ⟨environment,limits⟩ signaturesMatch slotsMatch batchBound created begun
    apply WP.spec_mono (compiler_body_wasm1_available ops law bound allocation started
      (EnvTranslation.context env w.ctx) w.body env w.ctx w.typeIdx w.ft point facts.localLayout facts.locals
      facts.functionSlots matched rfl facts.signatures results ⟨observed,indirect,simd,pool,fixups⟩
      signature w.context_results environment limits body room)
    intro result held
    obtain ⟨closed,reached,_,finished⟩ := held.2
    refine ⟨held.1,?_⟩
    simpa [finished,Slice.len] using reached.2
  | Wasm2 =>
    obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
      prepared_executable_safety_wasm2 ops law w room.size signaturesMatch slotsMatch batchBound created begun
    have contextEq : w.ctx = ⟨w.ctx.locals,w.ft.results⟩ := by
      have results : w.ctx.results = w.ft.results := alloc.vec.Vec.ext _ _ w.context_results
      cases h : w.ctx
      simp_all
    have accepted := compiler_body_wasm2_available ops law bound allocation started (EnvTranslation.context env w.ctx)
      (w.ctx.locals.val.map Translate.valueType) w.body env w.ctx.locals w.typeIdx w.ft point facts.localLayout
      facts.locals facts.functionSlots matched rfl facts.signatures ⟨observed,indirect,simd,pool,fixups⟩
      signature environment limits body (by simpa only [← contextEq] using room)
    rw [contextEq]
    apply WP.spec_mono accepted
    intro result held
    obtain ⟨closed,reached,_,finished⟩ := held.2
    refine ⟨held.1,?_⟩
    simpa [finished,Slice.len] using reached.2

end Exec.Code
