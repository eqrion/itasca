import Itasca.Runtime.Code.Local.Capacity.LocalAvailability
import Itasca.Runtime.Code.Local.Relations.Local.LocalDeclarations

namespace Itasca.Runtime.Code
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

end Itasca.Runtime.Code
