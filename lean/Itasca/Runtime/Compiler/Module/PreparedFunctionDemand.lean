import Itasca.Runtime.Compiler.Module.CodeRegionComplete
import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Module.Code.ReachedEntry
import Itasca.Module.Code.LocalsComplete
import Itasca.Runtime.Compiler.Local.Capacity.GlobalCapacity
import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment

/-!
Sections, each formerly its own module: CollectionAvailable, PreparedEntryReplay, PreparedFunctionDemand.
-/

/-! ## CollectionAvailable -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Moving a populated source slot into the dense vector succeeds when its
independently bounded append request is available. -/
theorem take_function_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (index : Usize) (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction)
    (function : runtime.bytecode.CompiledFunction)
    (inside : index.val < pending.val.length) (found : pending.val[index.val]? = some (some function))
    (capacity : functions.length < Usize.max) (reserve : functions.length+1 ≤ bound) :
    runtime.compiler.take_function ops budget pending index functions ⦃ out => out.1 = .Ok () ∧ out.2.1 = budget ∧
      out.2.2.1.val = pending.val.set index.val none ∧ out.2.2.2.val = functions.val++[function] ⦄ := by
  unfold runtime.compiler.take_function
  step as ⟨value,back,lookup,restore⟩
  have element : pending.val[index.val] = some function := (List.getElem?_eq_some_iff.mp found).2
  have valueEq : value = some function := lookup.trans element
  simp only [valueEq,element,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound allocation budget functions function capacity reserve
    as ⟨reply,afterBudget,afterFunctions,status,budgetEq,appended⟩
  subst reply afterBudget
  simp only [WP.spec_ok,restore,alloc.vec.Vec.set_val_eq]
  exact ⟨True.intro,True.intro,True.intro,appended⟩

/-- Every still-pending source slot is collected successfully. This internal
loop needs only populated slots and numerical reserve room, not a final
executable or successful collection supplied by its caller. -/
theorem collect_functions_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (functions : alloc.vec.Vec runtime.bytecode.CompiledFunction) (index : Usize)
    (inside : index.val ≤ pending.length) (collected : functions.length = index.val)
    (reserve : pending.length ≤ bound)
    (populated : ∀ next, index.val ≤ next → next < pending.length → ∃ function, pending.val[next]? = some (some function)) :
    runtime.compiler.collect_functions_loop ops budget pending functions index (.Ok ()) ⦃ out =>
      out.2.2.2 = .Ok () ∧ out.1 = budget ⦄ := by
  unfold runtime.compiler.collect_functions_loop
  apply loop.spec_decr_nat (fun state => pending.length-state.2.2.2.1.val)
    (fun state => state.1 = budget ∧ state.2.2.2.2 = .Ok () ∧ state.2.1.length = pending.length ∧
      state.2.2.2.1.val ≤ pending.length ∧ state.2.2.1.length = state.2.2.2.1.val ∧
      ∀ next, state.2.2.2.1.val ≤ next → next < pending.length →
        ∃ function, state.2.1.val[next]? = some (some function))
  · rintro ⟨currentBudget,currentPending,currentFunctions,currentIndex,status⟩ ⟨same,accepted,length,position,output,remaining⟩
    dsimp only at same accepted length position output remaining
    subst currentBudget status
    unfold runtime.compiler.collect_functions_loop.body
    simp only [bind_ok]
    split
    · rename_i more
      have inbounds : currentIndex.val < currentPending.length := by scalar_tac
      have originalBound : currentIndex.val < pending.length := by omega
      obtain ⟨function,found⟩ := remaining currentIndex.val (Nat.le_refl _) originalBound
      have capacity : currentFunctions.length < Usize.max := by
        have wordBound := pending.property
        change pending.length ≤ Usize.max at wordBound
        omega
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step with take_function_available ops bound allocation budget currentPending currentIndex currentFunctions function
        inbounds found capacity (by omega) as ⟨reply,afterBudget,afterPending,afterFunctions,success,budgetEq,pendingEq,appended⟩
      subst reply afterBudget
      step as ⟨next,increment⟩
      refine ⟨?_,?_,?_,?_,?_⟩
      · simp only [alloc.vec.Vec.length,pendingEq,List.length_set] at length ⊢
        exact length
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton] at output ⊢
        omega
      · intro selected lower upper
        rw [pendingEq,List.getElem?_set_ne (by omega)]
        exact remaining selected (by omega) upper
      · scalar_tac
    · exact WP.spec.ret ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl,inside,collected,populated⟩

/-- The actual dense collection succeeds in source order and preserves all
budget counters. Population is established by compilation's source-slot prefix. -/
theorem collect_functions_available {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (bound : Nat) (allocation : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (pending : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (reserve : pending.length ≤ bound)
    (populated : ∀ index, index < pending.length → ∃ function, pending.val[index]? = some (some function)) :
    runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧
      ∃ functions, out.1 = .Ok functions ∧ pending.val = functions.val.map some ⦄ := by
  have normal : runtime.compiler.collect_functions ops budget pending ⦃ out => out.2.1 = budget ∧ ∃ functions, out.1 = .Ok functions ⦄ := by
    unfold runtime.compiler.collect_functions
    step with collect_functions_loop_available ops bound allocation budget pending (alloc.vec.Vec.new _) 0#usize
      (by simp) (by simp [alloc.vec.Vec.new]) reserve (by intro index _ bound; exact populated index bound)
      as ⟨afterBudget,afterPending,functions,status,accepted,same⟩
    subst status afterBudget
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨True.intro,functions,rfl⟩
  obtain ⟨⟨reply,afterBudget,afterPending⟩,called,same,functions,accepted⟩ := WP.spec_imp_exists normal
  dsimp only at same accepted
  have ordered := collect_functions_spec ops law budget pending
  rw [called,WP.spec_ok] at ordered ⊢
  exact ⟨same,functions,accepted,ordered functions accepted⟩

end Itasca.Runtime.Compiler

end

/-! ## PreparedEntryReplay -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
set_option maxRecDepth 4096

/-- Exact prepared source bytes replay the actual entry parser around its two
visitor-bearing calls. This requires only those reached calls, rather than a
visitor that accepts arbitrary contexts or instruction traces. -/
theorem prepared_entry_replay {V : Type} (visitor : code.OpVisitor V)
    {data env index start} (w : CodeEntry.Prepared data env index start)
    (before started after : V)
    (begun : visitor.on_function_start before w.ctx w.typeIdx w.bodyStart w.finish = .ok (.Ok (),started))
    (body : code.validate_body_with visitor w.body env w.ctx w.typeIdx started = .ok (.Ok (),after)) :
    metadata.validate_code_entry_with visitor data start env index before
      ⦃ result => result = (.Ok w.finish,after) ⦄ := by
  have read := reader.read_u32_leb.complete data start w.size w.content w.header
  obtain ⟨declared,decoded,declaredValues⟩ := metadata.decode_locals.complete data w.content w.groups w.bodyStart
    w.locals_bytes w.locals_bound
  have indexBound : ¬ index ≥ alloc.vec.Vec.len env.func_type_indices := by
    have bound := w.index_lt
    scalar_tac
  unfold metadata.validate_code_entry_with
  simp [indexBound,read,core.result.Result.Insts.CoreOpsTry.branch]
  step
  obtain ⟨reply,haveBytes,haveBytesPost⟩ := WP.spec_imp_exists
    (metadata.have_bytes.spec data w.content n (by have bound := w.header.span; omega))
  have enough : reply = .Ok () := haveBytesPost.1.mpr (by have bound := w.body_bytes.bound; have extent := w.extent; scalar_tac)
  rw [enough] at haveBytes
  simp [haveBytes]
  step
  have endEq : «end» = w.finish := UScalar.eq_of_val_eq (by have extent := w.extent; scalar_tac)
  simp [decoded]
  have span := w.body_bytes.length
  have bodyStartBound : ¬ «end».val < w.bodyStart.val := by rw [endEq]; omega
  simp only [bodyStartBound,↓reduceIte]
  step
  have typeEq : type_idx = w.typeIdx := by simpa only [w.index_type] using type_idx_post
  step
  have typeBound : ¬ env.types.val.length ≤ t.val := by have bound := w.type_lt; rw [← typeEq] at bound; scalar_tac
  simp only [typeBound,↓reduceIte]
  step
  have functionEq : ft = w.ft := by
    simpa [t_post,typeEq,w.function_type] using ft_post
  have localRoom : ft.params.val.length+declared.val.length ≤ Usize.max := by
    rw [functionEq,declaredValues]
    have length := congrArg List.length w.context_locals
    simp only [List.length_append] at length
    have bound := w.ctx.locals.property
    omega
  obtain ⟨locals,build,localValues⟩ := WP.spec_imp_exists
    (metadata.build_func_locals.spec ft.params.deref declared.deref (by simpa [alloc.vec.Vec.deref] using localRoom))
  obtain ⟨results,copy,resultValues⟩ := WP.spec_imp_exists (metadata.copy_value_types.spec ft.results.deref)
  rw [build,copy]
  simp only [bind_ok]
  have localsEq : locals = w.ctx.locals := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,declaredValues,w.context_locals] using localValues)
  have resultsEq : results = w.ctx.results := alloc.vec.Vec.ext _ _ (by
    simpa [alloc.vec.Vec.deref,functionEq,w.context_results] using resultValues)
  have contextEq : (⟨locals,results⟩ : code.Context) = w.ctx := by rw [localsEq,resultsEq]
  rw [contextEq,typeEq,endEq,begun]
  simp only [bind_ok]
  step as ⟨actual,actualSpec⟩
  have bytes := ModuleBinary.slice_bytes (by have length := w.body_bytes.length; scalar_tac)
    w.body_bytes.bound actualSpec
  have bodyEq : actual = w.body := Slice.ext _ _ (by
    exact List.append_cancel_right (bytes.suffix.symm.trans w.body_bytes.suffix))
  rw [bodyEq,body]
  simp

end Itasca.Runtime.Compiler

end

/-! ## PreparedFunctionDemand -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Conservative function demand measured solely in source body bytes,
expanded local declarations, and independently validated operand peak. -/
structure PreparedFunctionDemand {A : Type} (budget : runtime.compiler.Budget A)
    (ctx : code.Context) (length peak bound : Nat) : Prop where
  size : length ≤ limits.MAX_FUNCTION_BYTES.val
  instructions : budget.instructions.val+3*length ≤ budget.limits.max_instructions.val
  branches : budget.branches.val+length ≤ budget.limits.max_branch_table_entries.val
  controls : budget.controls.val+1+length ≤ budget.limits.max_controls.val
  locals : budget.locals.val+ctx.locals.val.length ≤ budget.limits.max_locals.val
  temporary : 3*length+3 ≤ bound
  localReserve : ctx.locals.val.length ≤ bound
  operands : peak ≤ bound
  slots : 2*ctx.locals.val.length+2*peak ≤ U32.max

/-- Fresh compiler construction turns source-only demand into every reserve
and arithmetic premise of the actual function-start callback. -/
theorem PreparedFunctionDemand.start {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (ops : runtime.platform.Alloc A) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (batchStart : Usize) (initial : runtime.compiler.FunctionCompiler A)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial) :
    FunctionStartDemand initial ctx bound := by
  simp only [runtime.compiler.FunctionCompiler.new,Result.ok.injEq] at created
  subst initial
  have wordBound : U32.max ≤ Usize.max := by scalar_tac
  have localBound : ctx.locals.val.length ≤ Usize.max := by have slots := demand.slots; omega
  have one : 1 ≤ bound := by have temporary := demand.temporary; omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact demand.locals
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · simpa [alloc.vec.Vec.new] using localBound
  · simpa [alloc.vec.Vec.new] using demand.localReserve
  · have slots := demand.slots
    simp only [show (0#u32).val = 0 from rfl,Nat.zero_add]
    omega
  · change budget.controls.val < budget.limits.max_controls.val
    have controls := demand.controls
    omega
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one
  · simp [alloc.vec.Vec.new]; scalar_tac
  · simpa [alloc.vec.Vec.new] using one

/-- The actual start budget and local layout transfer the independent demand
into the complete body acceptance bound. -/
theorem PreparedFunctionDemand.body {A : Type}
    {budget : runtime.compiler.Budget A} {ctx length peak bound}
    (demand : PreparedFunctionDemand budget ctx length peak bound)
    (started : runtime.compiler.FunctionCompiler A) (usedLocals usedControls : Usize)
    (budgetFrame : started.budget = {budget with locals := usedLocals,controls := usedControls})
    (localsUsed : usedLocals.val = budget.locals.val+ctx.locals.val.length)
    (controlsUsed : usedControls.val = budget.controls.val+1)
    (layout : LocalLayout started) (localsMatch : started.function.locals = ctx.locals)
    (coordinate : started.function.body_start.val+length ≤ Usize.max) :
    BodyResourceRoom started length peak bound := by
  refine ⟨demand.size,?_,demand.temporary,demand.operands,?_,coordinate⟩
  · intro counter
    cases counter <;> simp only [ChargeCounter.used,ChargeCounter.limit,bodyResourceRate,budgetFrame,
      Nat.zero_mul,Nat.one_mul,localsUsed,controlsUsed]
    · exact demand.instructions
    · exact demand.branches
    · exact demand.controls
    · simpa only [Nat.add_zero] using demand.locals
  · have slotBound := slots_le_twice_length (compilerLocals started)
    have localLength : (compilerLocals started).length = ctx.locals.val.length := by
      simp [compilerLocals,localsMatch]
    rw [localLength] at slotBound
    rw [layout.slots]
    have room := demand.slots
    omega

end Itasca.Runtime.Compiler

end
