import Exec.Code.Module.PreparedFunctionAvailable
import Exec.Code.Module.PreparedBodyChecked

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual function-start and body compilation accept from independent source
validity and numerical demand. Initial prefix certificates and callback success
are constructed internally. The budget effect is relative to the entry budget,
so successive functions can share one module-wide bound. -/
theorem prepared_function_checked_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    {signatures : Slice runtime.compiler.Signature} {functionSlots : Slice U32}
    {budget : runtime.compiler.Budget A} {batchStart : Usize}
    {initial : runtime.compiler.FunctionCompiler A} {data env index start profile}
    (w : CodeEntry.Prepared data env index start profile)
    (limits : Profile.EnvironmentWithinLimits env)
    (body : Profile.Body profile w.body env w.ctx.locals w.typeIdx)
    (signaturesMatch : SignatureSequence signatures.val env.types.val)
    (slotsMatch : functionSlots.val.map (fun word => word.val) =
      env.func_types.val.map (fun ty => signatureSlots ty.params.val))
    (batchBound : batchStart.val+data.length ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (demand : PreparedFunctionDemand budget w.ctx w.body.length
      (independentBodyDemand w.body env w.ctx w.typeIdx).operands bound) :
    ∃ started,
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
        ops initial w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started) ∧
      code.validate_body_with (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) w.body env w.ctx
        w.typeIdx profile started ⦃ result => result.1 = .Ok () ∧
          CompilationBudgetEffect budget result.2.budget (preparedFunctionAllowance w.ctx w.body.length) ∧
          FunctionPublicationRanges result.2.function ∧ CheckedInstructionPrefix result.2.function ⦄ := by
  have signature : env.types.val[w.typeIdx.val]? = some w.ft := by
    simp only [List.getElem?_eq_getElem w.type_lt,w.function_type]
  obtain ⟨sig,lookup,signatureMatch⟩ := signaturesMatch.lookup_source signature
  have fresh := compiler_new ops signatures functionSlots budget batchStart
  rw [created,WP.spec_ok] at fresh
  obtain ⟨localLayout,locals,operands,controls,frames,code,reachable,sigs,slots,batch⟩ := fresh
  have budgetEq : initial.budget = budget := by
    simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
    subst initial
    rfl
  have endFits : batchStart.val+w.finish.val ≤ Usize.max := by
    have last := w.body_bytes.bound
    omega
  have beginFits : batchStart.val+w.bodyStart.val ≤ Usize.max := by
    have length := w.body_bytes.length
    omega
  obtain ⟨⟨status,started⟩,begun,accepted,usedLocals,usedControls,budgetFrame,localsUsed,controlsUsed⟩ := WP.spec_imp_exists
    (compiler_function_start_available ops bound allocation initial w.ctx w.typeIdx sig w.bodyStart w.finish
      (by simpa only [sigs] using lookup) (by simpa only [batch] using beginFits)
      (by simpa only [batch] using endFits) (demand.start ops signatures functionSlots batchStart initial created))
  dsimp only at accepted budgetFrame localsUsed controlsUsed
  subst status
  rw [budgetEq] at budgetFrame localsUsed controlsUsed
  obtain ⟨layout,localsMatch,_,_,_,bodyStart,_⟩ := compiler_function_start_facts ops law signatures functionSlots budget batchStart
    initial started w.ctx w.typeIdx sig w.bodyStart w.finish lookup beginFits endFits created begun
  have room := demand.body started usedLocals usedControls budgetFrame localsUsed controlsUsed layout localsMatch
    (function_body_coordinate_bound w.body_bytes bodyStart endFits)
  refine ⟨started,begun,?_⟩
  apply WP.spec_mono (prepared_body_checked_available ops law bound allocation w limits body signaturesMatch slotsMatch
    batchBound created begun room)
  intro result held
  refine ⟨held.1,?_,held.2.2⟩
  have startEffect : CompilationBudgetEffect budget started.budget
      (fun counter => match counter with | .locals => w.ctx.locals.val.length | .controls => 1 | _ => 0) := by
    rw [budgetFrame]
    refine ⟨rfl,rfl,?_⟩
    intro counter
    cases counter <;> simp [ChargeCounter.used,localsUsed,controlsUsed]
  exact (startEffect.trans held.2.1).weaken (by intro counter; cases counter <;> simp [bodyResourceRate,preparedFunctionAllowance])

end Itasca.Runtime.Code
