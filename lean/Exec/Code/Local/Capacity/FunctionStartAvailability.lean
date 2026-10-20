import Exec.Code.Local.Capacity.LocalLoopAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent resource demand of function-start setup, including expanded
locals, word slots, offsets, the root map, and its physical frame. -/
structure FunctionStartDemand {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (bound : Nat) : Prop where
  localsRoom : compiler.budget.locals.val + ctx.locals.val.length ≤ compiler.budget.limits.max_locals.val
  localsCapacity : compiler.function.locals.length + ctx.locals.val.length ≤ Usize.max
  localsReserve : compiler.function.locals.length + ctx.locals.val.length ≤ bound
  offsetCapacity : compiler.local_offsets.length + ctx.locals.val.length ≤ Usize.max
  offsetReserve : compiler.local_offsets.length + ctx.locals.val.length ≤ bound
  slots : compiler.function.local_slots.val + 2*ctx.locals.val.length ≤ U32.max
  controlsRoom : compiler.budget.controls.val < compiler.budget.limits.max_controls.val
  mapsCapacity : compiler.function.controls.length < Usize.max
  mapsReserve : compiler.function.controls.length+1 ≤ bound
  framesCapacity : compiler.frames.length < Usize.max
  framesReserve : compiler.frames.length+1 ≤ bound

/-- The actual function-start callback accepts under independent signature,
coordinate, and resource bounds. It changes precisely the local and root-control
budget counters, preserving every other budget field. -/
theorem compiler_function_start_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (signature : runtime.compiler.Signature) (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val+bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val+bodyEnd.val ≤ Usize.max)
    (demand : FunctionStartDemand compiler ctx bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
        out.1 = .Ok () ∧ ∃ usedLocals usedControls,
          out.2.budget = {compiler.budget with locals := usedLocals,controls := usedControls} ∧
          usedLocals.val = compiler.budget.locals.val+ctx.locals.val.length ∧
          usedControls.val = compiler.budget.controls.val+1 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
  step as ⟨start,startEq⟩
  step as ⟨finish,finishEq⟩
  step as ⟨index,indexEq⟩
  have signatureBound := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨actual,found⟩
  have sameSignature : actual = signature := by
    simpa [indexEq,found,List.getElem?_eq_getElem signatureBound] using lookup
  rw [sameSignature]
  let initial := {compiler with function := {compiler.function with
    param_slots := signature.param_slots,type_index := typeIndex,body_start := start,body_end := finish}}
  obtain ⟨out,call,updated,same,frame,budgetFrame,locals,offsets,used,words⟩ := WP.spec_imp_exists
    (compiler_locals_available ops bound available initial ctx 0#usize (by simp)
      (by simpa [initial] using demand.localsRoom) (by simpa [initial] using demand.localsCapacity)
      (by simpa [initial] using demand.localsReserve) (by simpa [initial] using demand.offsetCapacity)
      (by simpa [initial] using demand.offsetReserve) (by simpa [initial] using demand.slots))
  rw [same] at call
  rw [call]
  simp only [localLoopOutput,uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have maps : updated.function.controls = compiler.function.controls := by
    have held := congrArg (fun value => value.function.controls) frame
    exact held
  have frames : updated.frames = compiler.frames := congrArg (fun value => value.frames) frame
  have retainedControls : updated.budget.controls = compiler.budget.controls := congrArg (fun value => value.controls) budgetFrame
  have retainedLimits : updated.budget.limits = compiler.budget.limits := congrArg (fun value => value.limits) budgetFrame
  have expectedBudget : updated.budget = {compiler.budget with locals := updated.budget.locals} := budgetFrame
  clear frame budgetFrame
  step with charge_counter_available ops .controls updated.budget
    (by simpa [ChargeCounter.used,ChargeCounter.limit,retainedControls,retainedLimits] using demand.controlsRoom)
    as ⟨status,charged,accepted,usedControls,sameBudget,chargedEq⟩
  rw [accepted]
  rw [expectedBudget] at sameBudget
  subst charged
  clear expectedBudget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available
    ({compiler.budget with locals := updated.budget.locals,controls := usedControls}) updated.function.controls
    ⟨.Body,updated.function.body_start,0#usize,0#usize,0#usize,0#usize,0#usize,signature.results⟩
    (by simpa [maps] using demand.mapsCapacity) (by simpa [maps] using demand.mapsReserve)
    as ⟨status,charged,mapsOut,accepted,sameBudget,appendedMaps⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available
    ({compiler.budget with locals := updated.budget.locals,controls := usedControls}) updated.frames
    ⟨0#usize,.Body,updated.function.local_slots,0#u32,signature.result_slots,0#u32,none,true,false,alloc.vec.Vec.new _⟩
    (by simpa [frames] using demand.framesCapacity) (by simpa [frames] using demand.framesReserve)
    as ⟨status,charged,framesOut,accepted,sameBudget,appendedFrames⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
  refine ⟨trivial,updated.budget.locals,usedControls,rfl,?_,?_⟩
  · simpa [initial] using used
  · simpa [retainedControls] using chargedEq

end Exec.Code
