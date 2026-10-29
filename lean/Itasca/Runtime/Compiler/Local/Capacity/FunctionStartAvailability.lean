import Itasca.Runtime.Compiler.Local.Capacity.ChargeAvailability
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations

/-!
Availability of function start, from a single local allocation through the local-declaration loop. FunctionStartDemand records the bounds consumed by the entry construction.
-/

/-! ## Local Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- One local declaration accepts from independently bounded reserves, word
width, and remaining local budget. Its exact frame retains every other compiler
field and budget counter. -/
theorem compiler_add_local_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (type : Itasca.types.ValueType)
    (room : compiler.budget.locals.val < compiler.budget.limits.max_locals.val)
    (localsCapacity : compiler.function.locals.length < Usize.max)
    (localsRequest : compiler.function.locals.length + 1 ≤ bound)
    (offsetCapacity : compiler.local_offsets.length < Usize.max)
    (offsetRequest : compiler.local_offsets.length + 1 ≤ bound)
    (slots : compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ≤ U32.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler type ⦃ out =>
      out.1 = .Ok () ∧ ∃ locals offsets localSlots used,
        out.2 = {compiler with
          budget := {compiler.budget with locals := used}
          function := {compiler.function with locals,local_slots := localSlots}
          local_offsets := offsets} ∧
        locals.val = compiler.function.locals.val ++ [type] ∧
        offsets.val = compiler.local_offsets.val ++ [compiler.function.local_slots] ∧
        localSlots.val = compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ∧
        used.val = compiler.budget.locals.val + 1 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.add_local
  step with charge_counter_available ops .locals compiler.budget room
    as ⟨status,charged,accepted,used,same,usedEq⟩
  rw [accepted]
  subst charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.local_offsets compiler.function.local_slots offsetCapacity offsetRequest
    as ⟨status,charged,offsets,accepted,same,appendedOffsets⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.function.locals type localsCapacity localsRequest
    as ⟨status,charged,locals,accepted,same,appendedLocals⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_width type as ⟨word,wordEq⟩
  step as ⟨added,addSpec⟩
  cases added with
  | none => scalar_tac
  | some localSlots =>
    simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨trivial,locals,offsets,localSlots,used,rfl,appendedLocals,appendedOffsets,by scalar_tac,usedEq⟩

end Itasca.Runtime.Compiler

end

/-! ## Local Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The actual local declaration loop accepts independently bounded remaining
source locals, preserving the complete nonlocal compiler and budget frames. -/
theorem compiler_locals_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context) (index : Usize)
    (inside : index.val ≤ ctx.locals.val.length)
    (room : compiler.budget.locals.val + (ctx.locals.val.length-index.val) ≤ compiler.budget.limits.max_locals.val)
    (localsCapacity : compiler.function.locals.length + (ctx.locals.val.length-index.val) ≤ Usize.max)
    (localsReserve : compiler.function.locals.length + (ctx.locals.val.length-index.val) ≤ bound)
    (offsetCapacity : compiler.local_offsets.length + (ctx.locals.val.length-index.val) ≤ Usize.max)
    (offsetReserve : compiler.local_offsets.length + (ctx.locals.val.length-index.val) ≤ bound)
    (slots : compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val) ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop ops compiler ctx index (.Ok ())
      ⦃ out => ∃ after, out = localLoopOutput after (.Ok ()) ∧ LocalFrame compiler after ∧
        after.budget = {compiler.budget with locals := after.budget.locals} ∧
        after.function.locals.length = compiler.function.locals.length + (ctx.locals.val.length-index.val) ∧
        after.local_offsets.length = compiler.local_offsets.length + (ctx.locals.val.length-index.val) ∧
        after.budget.locals.val = compiler.budget.locals.val + (ctx.locals.val.length-index.val) ∧
        after.function.local_slots.val ≤ compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
  apply loop.spec_decr_nat (fun state => ctx.locals.val.length-state.2.1.val)
    (fun state => LocalFrame compiler state.1 ∧
      state.1.budget = {compiler.budget with locals := state.1.budget.locals} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ ctx.locals.val.length ∧
      state.1.function.locals.length + (ctx.locals.val.length-state.2.1.val) =
        compiler.function.locals.length + (ctx.locals.val.length-index.val) ∧
      state.1.local_offsets.length + (ctx.locals.val.length-state.2.1.val) =
        compiler.local_offsets.length + (ctx.locals.val.length-index.val) ∧
      state.1.budget.locals.val + (ctx.locals.val.length-state.2.1.val) =
        compiler.budget.locals.val + (ctx.locals.val.length-index.val) ∧
      state.1.function.local_slots.val + 2*(ctx.locals.val.length-state.2.1.val) ≤
        compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨frame,budgetFrame,accepted,position,localCount,offsetCount,used,words⟩
    dsimp only at frame budgetFrame accepted position localCount offsetCount used words
    subst status
    have limits : current.budget.limits = compiler.budget.limits := congrArg (fun value => value.limits) budgetFrame
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body
    dsimp only
    split
    · rename_i more
      have atLocal : next.val < ctx.locals.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step as ⟨type,found⟩
      have widthBound : width (Itasca.Translate.valueType type) ≤ 2 := by cases type <;> decide
      step with compiler_add_local_available ops bound available current type
        (by rw [limits]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        as ⟨status,after,accepted,locals,offsets,localSlots,charged,shape,appendedLocals,appendedOffsets,slotEq,chargedEq⟩
      subst status after
      have nextFrame : LocalFrame compiler {current with
          budget := {current.budget with locals := charged}
          function := {current.function with locals,local_slots := localSlots}
          local_offsets := offsets} := frame.trans rfl
      have nextBudget : {current.budget with locals := charged} = {compiler.budget with locals := charged} := by
        rw [budgetFrame]
      clear frame budgetFrame
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
      · exact nextFrame
      · exact nextBudget
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appendedLocals,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at localCount
        omega
      · simp only [alloc.vec.Vec.length,appendedOffsets,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at offsetCount
        omega
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = ctx.locals.val.length := by
        have ended : ctx.locals.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,frame,budgetFrame,by simpa [last] using localCount,
        by simpa [last] using offsetCount,by simpa [last] using used,by simpa [last] using words⟩
  · exact ⟨.refl _,rfl,rfl,inside,rfl,rfl,rfl,by dsimp only; omega⟩

end Itasca.Runtime.Compiler

end

/-! ## Function Start Availability -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end
