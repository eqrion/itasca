import Exec.Code.Module.PreparedExecutableSafety
import Exec.Code.Body.Relations.Common.BodyCheckedWasm2
import Exec.Code.Module.PreparedPublicationStart
import Exec.Code.Local.Checking.FunctionStartExitSlots

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent validity and source-only allocation/resource room establish
actual body success and every final source/control-target range check. Initial
publication bounds are constructed from actual fresh function-start internally. -/
theorem prepared_body_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial started : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Profile.Body profile w.body env w.ctx.locals w.typeIdx)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (begun : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (room : BodyResourceRoom started w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound) :
    code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body env w.ctx
      w.typeIdx profile started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨coordinates,maps,targets,extent⟩ := prepared_start_publication ops law w signaturesMatch batchBound created begun
  obtain ⟨sig,lookup,_⟩ := signaturesMatch.lookup_source signature
  have endFits : batchStart.val+w.finish.val ≤ Usize.max := by
    have bound := w.body_bytes.bound
    omega
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  have instructions := compiler_start_instruction_prefix ops law signatures functionSlots budget batchStart initial started w.ctx
    w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  have exits := compiler_start_exit_slots ops law signatures functionSlots budget batchStart initial started w.ctx
    w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  obtain ⟨facts,matched,point,observed,indirect,simd,pool,fixups⟩ :=
    prepared_executable_safety_wasm2 ops law w room.size signaturesMatch slotsMatch batchBound created begun
  have contextEq : w.ctx = ⟨w.ctx.locals,w.ft.results⟩ := by
    have results : w.ctx.results = w.ft.results := alloc.vec.Vec.ext _ _ w.context_results
    cases h : w.ctx
    simp_all
  have accepted := compiler_body_wasm2_checked_available ops law bound allocation started (EnvTranslation.context env w.ctx)
    (w.ctx.locals.val.map Translate.valueType) w.body env w.ctx.locals w.typeIdx w.ft point facts.localLayout
    facts.locals facts.functionSlots matched rfl facts.signatures ⟨observed,indirect,simd,pool,fixups⟩
    limits body.to_wasm2 (by simpa only [← contextEq] using room) coordinates maps targets
    (by simp only [compilerLocals,facts.locals]) (by rw [facts.capacity]) instructions exits extent
  rw [← contextEq] at accepted
  have checked : code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body
      env w.ctx w.typeIdx .Wasm2 started ⦃ result => result.1 = .Ok () ∧
        SourceCompilationBudget started.budget result.2.budget bodyResourceRate w.body.length ∧
        FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
    apply WP.spec_mono accepted
    intro result held
    obtain ⟨closed,reached,closedState,finished⟩ := held.2
    refine ⟨held.1,?_,reached.1.final_ranges closedState,reached.2.2.2 closedState⟩
    simpa [finished,Slice.len] using reached.1.1.2
  cases profile with
  | Wasm2 => exact checked
  | Wasm1 =>
    obtain ⟨result,run,post⟩ := WP.spec_imp_exists checked
    rw [code.validate_body_with.wasm1_of_body _ _ _ _ _ _ result limits room.size body run, WP.spec_ok]
    exact post

end Exec.Code
