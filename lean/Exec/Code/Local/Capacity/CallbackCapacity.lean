import Exec.Code.Local.Capacity.CopyBudgetAvailability

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Independent room for a callback that emits several instructions. The final
PC is representable too, so guard patches can name the point after emission. -/
structure CallbackCapacity {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bound count : Nat) : Prop where
  pc : compiler.function.code.length + count ≤ U32.max
  codeCapacity : compiler.function.code.length + count ≤ Usize.max
  sourceCapacity : compiler.function.source_offsets.length + count ≤ Usize.max
  codeReserve : compiler.function.code.length + count ≤ bound
  sourceReserve : compiler.function.source_offsets.length + count ≤ bound
  coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max
  instructions : compiler.budget.instructions.val + count ≤ compiler.budget.limits.max_instructions.val
  operands : state.vals.length ≤ bound
  slots : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max

theorem CallbackCapacity.mono {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count smaller} (capacity : CallbackCapacity compiler state bound count)
    (less : smaller ≤ count) : CallbackCapacity compiler state bound smaller := by
  rcases capacity with ⟨pc,code,sources,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  exact ⟨by omega,by omega,by omega,by omega,by omega,coordinate,by omega,operands,slots⟩

/-- At least one remaining instruction pays for an ordinary emission. -/
theorem CallbackCapacity.one {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count} (capacity : CallbackCapacity compiler state bound count)
    (positive : 0 < count) : CallbackDemand compiler state bound := by
  rcases capacity with ⟨pc,code,sources,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  exact ⟨by omega,by omega,by omega,by omega,by omega,coordinate,by omega,operands,slots⟩

/-- One emitted instruction consumes one unit of the independently reserved
capacity. Unchanged compiler fields follow from the exact emission frame. -/
theorem CallbackCapacity.after_emission {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state bound count instruction} (capacity : CallbackCapacity before state bound (count+1))
    (emitted : Emitted before after instruction)
    (effect : CompilationBudgetEffect before.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) :
    CallbackCapacity after state bound count := by
  obtain ⟨budget,code,sources,frame,appended,recorded⟩ := emitted
  have codeCount : code.length = before.function.code.length+1 := by simp [alloc.vec.Vec.length,appended]
  have sourceCount : sources.length = before.function.source_offsets.length+1 := by
    have lengths := congrArg List.length recorded
    simpa [alloc.vec.Vec.length] using lengths
  have limits := effect.limits
  have used := (effect.counts .instructions).2
  rw [frame] at limits used ⊢
  simp only [ChargeCounter.used,↓reduceIte] at used
  rcases capacity with ⟨pc,codeCapacity,sourceCapacity,codeReserve,sourceReserve,coordinate,instructions,operands,slots⟩
  refine ⟨?_,?_,?_,?_,?_,coordinate,?_,operands,slots⟩
  · change code.length + count ≤ U32.max; omega
  · change code.length + count ≤ Usize.max; omega
  · change sources.length + count ≤ Usize.max; omega
  · change code.length + count ≤ bound; omega
  · change sources.length + count ≤ bound; omega
  · change budget.instructions.val + count ≤ budget.limits.max_instructions.val
    rw [limits]
    omega

/-- Replacing control frames leaves the emission and observation demand
unchanged. Label updates do not alter code, slots, or resource counters. -/
theorem CallbackCapacity.with_frames {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {state bound count} (capacity : CallbackCapacity compiler state bound count)
    (frames : alloc.vec.Vec runtime.compiler.Frame) :
    CallbackCapacity {compiler with frames} state bound count :=
  ⟨capacity.pc,capacity.codeCapacity,capacity.sourceCapacity,capacity.codeReserve,
    capacity.sourceReserve,capacity.coordinate,capacity.instructions,capacity.operands,capacity.slots⟩

end Exec.Code
