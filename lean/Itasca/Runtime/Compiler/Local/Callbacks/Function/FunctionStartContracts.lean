import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations

/-! Contracts for function entry: local declarations and root control publication. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

/-- Function setup changes local declarations, entry coordinates and root control
state while retaining all buffers and environment used by ordinary callbacks. -/
def FunctionStartFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = {before with
    budget := after.budget,
    function := {before.function with
      param_slots := after.function.param_slots, type_index := after.function.type_index,
      body_start := after.function.body_start, body_end := after.function.body_end,
      locals := after.function.locals, local_slots := after.function.local_slots,
      slot_count := after.function.slot_count, controls := after.function.controls},
    frames := after.frames, height := after.height, local_offsets := after.local_offsets}

/-- Every normal function-start result retains the non-entry state. No allocator
law or successful status is required for this structural inversion. -/
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.inv
    {A : Type} (ops : runtime.platform.Alloc A)
    (before after : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (bodyBegin bodyEnd : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex bodyBegin bodyEnd = .ok (status, after)) :
    FunctionStartFrame before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start at called
  simp only [lift, bind_ok, Std.bind_assoc] at called
  obtain ⟨start, _, rest⟩ := bind_ok_inv _ _ _ called
  obtain ⟨finish, _, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨signature, _, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨output, locals, rest⟩ := bind_ok_inv _ _ _ rest
  obtain ⟨updated, result, same, frame⟩ :=
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.inv
      ops _ ctx 0#usize (.Ok ()) locals
  subst output
  simp only [localLoopOutput, uncurry_apply_pair] at rest
  unfold LocalFrame at frame
  cases result with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    obtain ⟨rfl, rfl⟩ := rest
    unfold FunctionStartFrame
    rw [frame]
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc] at rest
    obtain ⟨⟨charged, budget⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    simp only [uncurry_apply_pair] at rest
    cases charged with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      obtain ⟨rfl, rfl⟩ := rest
      unfold FunctionStartFrame
      rw [frame]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc] at rest
      obtain ⟨⟨pushed, nextBudget, maps⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      simp only [uncurry_apply_pair] at rest
      cases pushed with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        unfold FunctionStartFrame
        rw [frame]
      | Ok unit =>
        cases unit
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Std.bind_assoc] at rest
        obtain ⟨⟨pushed, finalBudget, frames⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair] at rest
        cases pushed with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, rfl⟩ := rest
          unfold FunctionStartFrame
          rw [frame]
        | Ok unit =>
          cases unit
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, rfl⟩ := rest
          unfold FunctionStartFrame
          rw [frame]

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

structure FunctionStartInputs {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (typeIndex : U32) (signature : runtime.compiler.Signature) (bodyBegin bodyEnd : Usize) : Prop where
  lookup : compiler.signatures.val[typeIndex.val]? = some signature
  beginFits : compiler.batch_start.val + bodyBegin.val ≤ Usize.max
  endFits : compiler.batch_start.val + bodyEnd.val ≤ Usize.max
  emptyLocals : compiler.function.locals.val = []
  localLayout : LocalLayout compiler
  emptyOperands : compiler.before.val = []
  mapsFit : compiler.function.controls.val.length < Usize.max
  framesFit : compiler.frames.val.length < Usize.max

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (inputs : FunctionStartInputs compiler typeIndex signature bodyBegin bodyEnd) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ (status, after) =>
      status = .Ok () → CompilerLayout after [] ∧
        after.reachable = compiler.reachable ∧
        after.function.slot_count = after.function.local_slots ∧
        after.function.locals.val = ctx.locals.val ∧
        after.function.param_slots = signature.param_slots ∧
        after.function.type_index = typeIndex ∧
        after.function.body_start.val = compiler.batch_start.val + bodyBegin.val ∧
        after.function.body_end.val = compiler.batch_start.val + bodyEnd.val ∧
        after.function.code = compiler.function.code ∧
        after.frames.val = compiler.frames.val ++
          [⟨0#usize, .Body, after.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Body, after.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize,
            0#usize, signature.results⟩] ⦄ := by
  rcases inputs with ⟨lookup, beginFits, endFits, emptyLocals, localLayout, emptyOperands, mapsFit, framesFit⟩
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
  step as ⟨start, startEq⟩
  step as ⟨finish, finishEq⟩
  step as ⟨index, indexEq⟩
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨sig, sigEq⟩
  have same : sig = signature := by simpa [indexEq, sigEq, List.getElem?_eq_getElem bound] using lookup
  rw [same]
  let initial := { compiler with function := { compiler.function with param_slots := signature.param_slots, type_index := typeIndex, body_start := start, body_end := finish } }
  have initialLayout : LocalLayout initial := ⟨localLayout.slots, localLayout.offsets⟩
  step with compiler_locals_loop ops law initial ctx 0#usize (by simp) initialLayout
    (by simpa [initial] using emptyLocals)
    as ⟨s, s1, b, i3, cf, v, b1, i4, v1, i5, v2, v3, result, updated, status, outputEq, certified⟩
  simp only [localLoopOutput, Prod.mk.injEq] at outputEq
  rcases outputEq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨frame, layout, types⟩ := certified rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_control ops updated.budget as ⟨status, budget⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have sameControls : updated.function.controls = compiler.function.controls := by rw [frame]
      have sameFrames : updated.frames = compiler.frames := by rw [frame]
      step with budget_push ops law budget updated.function.controls
        ⟨.Body, updated.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, signature.results⟩
        (by simpa [sameControls] using mapsFit) as ⟨status, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [bind_ok]
        step with budget_push ops law budget1 updated.frames
          ⟨0#usize, .Body, updated.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
          (by simpa [sameFrames] using framesFit) as ⟨status, budget2, frames, pushed⟩
        rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [bind_ok, WP.spec_ok]
          intro accepted
          refine ⟨⟨layout.slots, layout.offsets, ?_, ?_, ?_⟩, ?_, rfl, types, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have : updated.before = compiler.before := by rw [frame]
            simp [this, emptyOperands, stackOffsets]
          · simp only [compilerLocals, slots, Nat.add_zero]
            exact layout.slots
          · intro _; exact Nat.le_refl _
          · rw [frame]
          · rw [frame]
          · rw [frame]
          · rw [frame]; exact startEq
          · rw [frame]; exact finishEq
          · rw [frame]
          · simpa [sameFrames] using frameAppend
          · simpa [sameControls] using mapAppend
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]


theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (typeIndex : U32) (signature : runtime.compiler.Signature) (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val+bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val+bodyEnd.val ≤ Usize.max)
    (demand : FunctionStartDemand compiler ctx bound) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ (status, after) =>
        status = .Ok () ∧ ∃ usedLocals usedControls,
          after.budget = {compiler.budget with locals := usedLocals,controls := usedControls} ∧
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
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.available ops bound available initial ctx 0#usize (by simp)
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
  refine ⟨rfl,updated.budget.locals,usedControls,rfl,?_,?_⟩
  · simpa [initial] using used
  · simpa [retainedControls] using chargedEq


end Itasca.Runtime.Compiler
