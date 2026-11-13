import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Initializer.InitializerExpressionAvailable
import Itasca.Runtime.Compiler.Local.Relations.Table.BranchTableCallback
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Capacity.IndependentBodyReplay
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering

/-!
Sections, each formerly its own module: FunctionStartAvailability, SlotAvailability, BranchTableCapacity, GlobalCapacity.
-/

/-! ## FunctionStartAvailability -/

section

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
    (compiler : runtime.compiler.FunctionCompiler A) (type : Itasca.wasm_types.ValueType)
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

end

/-! ## SlotAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The executable slot-range gate accepts an independent arithmetic bound. -/
theorem slots_fit_accepts (function : runtime.bytecode.CompiledFunction) (start count : U32)
    (bounded : start.val + count.val ≤ function.slot_count.val) :
    runtime.bytecode.CompiledFunction.slots_fit function start count = .ok true := by
  have lower : start ≤ function.slot_count := by scalar_tac
  have accepts : runtime.bytecode.CompiledFunction.slots_fit function start count ⦃ result => result = true ⦄ := by
    unfold runtime.bytecode.CompiledFunction.slots_fit
    rw [if_pos lower]
    step as ⟨remaining,difference⟩
    have fits : count ≤ remaining := by scalar_tac
    simp [fits]
  obtain ⟨result,actual,rfl⟩ := WP.spec_imp_exists accepts
  exact actual

/-- Initializer instructions remain accepted in a larger final slot capacity,
as needed when composing active segment programs. -/
theorem initial_instruction_capacity_accepts (function : runtime.bytecode.CompiledFunction)
    (expr : Itasca.wasm_types.ConstExpr) (ty : Itasca.wasm_types.ValueType) (instruction : runtime.bytecode.Instr)
    (lowered : InitialInstruction function expr ty instruction)
    (capacity : (initializerWidth ty).val ≤ function.slot_count.val)
    (vector : ∀ lo hi, expr = .V128 lo hi → ty = .V128) :
    runtime.bytecode.CompiledFunction.instruction_valid function instruction = .ok true := by
  have scalar : runtime.bytecode.CompiledFunction.slots_fit function 0#u32 1#u32 = .ok true := by
    apply slots_fit_accepts
    have positive : 1 ≤ (initializerWidth ty).val := by cases ty <;> decide
    scalar_tac
  have wide (same : ty = .V128) :
      runtime.bytecode.CompiledFunction.slots_fit function 0#u32 2#u32 = .ok true := by
    apply slots_fit_accepts
    simpa [same,initializerWidth] using capacity
  cases lowered <;>
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,
      runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok]
  all_goals first | exact scalar | exact wide rfl | skip
  rename_i lo hi pool embedded
  rw [wide (vector lo hi rfl),bind_ok]
  have inside := (List.getElem?_eq_some_iff.mp embedded).1
  simpa [lift] using inside

end Itasca.Runtime.Compiler

end

/-! ## BranchTableCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

theorem compiler_table_branch_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (index : Usize) (depth : U32) (lookup : before.table_depths.val[index.val]?=some depth)
    (accepted : runtime.compiler.control.FunctionCompiler.table_branch ops before index=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨target,budget,table,_,_,called⟩ := compiler_table_branch_success ops law before after index depth lookup accepted
  exact compiler_branch_capacity ops law {before with budget,function:={before.function with jump_tables:=table}}
    after depth 1#u32 false called

theorem TableBranchRun.capacity {A : Type} {ops : runtime.platform.Alloc A}
    (law : Platform.AllocCorrect ops) {before after : runtime.compiler.FunctionCompiler A}
    {index : Nat} (run : TableBranchRun ops before index after) :
    capacityMetadata after=capacityMetadata before := by
  induction run with
  | done => rfl
  | @cons before middle after index inside called rest ih =>
    exact ih.trans (compiler_table_branch_capacity ops law before middle index before.table_depths.val[index.val]
      (List.getElem?_eq_getElem inside) called)

theorem compiler_lower_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.lower_table_branches ops before=.ok (.Ok (),after)) :
    capacityMetadata after=capacityMetadata before := by
  obtain ⟨start,len,selector,emitted,_,_,_,emission,run⟩ := compiler_lower_table_success ops law before after accepted
  have retained := run.capacity law
  obtain ⟨budget,code,sources,rfl,_,_⟩ := emission
  exact retained

theorem compiler_br_table_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (fallback : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table
      ops before state fallback types=.ok (.Ok (),after)) :
    CapacityStep before after state := by
  by_cases live : before.reachable=true
  · obtain ⟨budget,depths,lowered,cleared,_,called,_,observed⟩ :=
      compiler_br_table_success ops law before after state fallback types live accepted
    have retained := compiler_lower_table_capacity ops law {before with budget,table_depths:=depths} lowered called
    have fields : lowered.function.local_slots=before.function.local_slots ∧
        lowered.function.slot_count=before.function.slot_count := by
      simpa only [capacityMetadata,Prod.mk.injEq] using retained
    have effect := compiler_observe_capacity_bound ops law {lowered with reachable:=false,table_depths:=cleared}
      after state (.Ok ()) observed
    exact ⟨effect.1.trans fields.1,by simpa only [fields.1,fields.2] using effect.2 rfl⟩
  · have dead := Bool.eq_false_iff.mpr live
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_table at accepted
    obtain ⟨⟨result,labeled⟩,called,rest⟩ := bind_ok_inv _ _ _ accepted
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok unit =>
      cases unit
      obtain ⟨budget,depths,rfl,_⟩ := compiler_table_label_success ops law before labeled state fallback called
      simp only [uncurry_apply_pair,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,dead,Bool.false_eq_true,ite_false] at rest
      obtain ⟨cleared,_,observed⟩ := bind_ok_inv _ _ _ rest
      have effect := compiler_observe_capacity_bound ops law {before with budget,table_depths:=cleared} after state (.Ok ())
        (by simpa only [dead] using observed)
      exact ⟨effect.1,effect.2 rfl⟩
end Itasca.Runtime.Compiler

end

/-! ## GlobalCapacity -/

section

set_option maxHeartbeats 1200000
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

theorem global_get_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (ty : valtype) (dst index : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled
      (globalGetInstruction (decide (width ty = 2)) dst index) = .ok true) :
    dst.val + width ty ≤ compiled.slot_count.val := by
  by_cases vector : width ty = 2
  · simp only [vector,decide_true,globalGetInstruction,ite_true] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 2#u32 checked
    rw [vector]
    scalar_tac
  · have widthEq : width ty = 1 := by cases ty <;> simp_all [width]
    simp only [widthEq,globalGetInstruction,show decide (1=2) = false from rfl,Bool.false_eq_true,ite_false] at checked
    simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,runtime.bytecode.Instr.scalar,runtime.bytecode.Instr.load,runtime.bytecode.Instr.store,runtime.bytecode.Instr.simd,bind_ok] at checked
    have bound := slots_fit_true compiled dst 1#u32 checked
    rw [widthEq]
    scalar_tac

end Itasca.Runtime.Compiler

end
