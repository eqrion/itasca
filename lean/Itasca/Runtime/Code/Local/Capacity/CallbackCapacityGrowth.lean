import Itasca.Runtime.Code.Local.Capacity.CallbackCapacity

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- A bounded internal lowering step consumes its numeric allowance without
requiring a single-emission shape. This applies to branch-table stubs, whose
fixup updates and optional copies have separate checked structural effects. -/
theorem CallbackCapacity.after_growth {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state bound count amount} (capacity : CallbackCapacity before state bound (count+amount))
    (code : after.function.code.length ≤ before.function.code.length+amount)
    (sources : after.function.source_offsets.length ≤ before.function.source_offsets.length+amount)
    (localsSame : after.function.local_slots = before.function.local_slots)
    (coordinate : after.function.body_start.val+after.next_source.val ≤ Usize.max)
    (effect : CompilationBudgetEffect before.budget after.budget
      (fun counter => if counter = .instructions then amount else 0)) :
    CallbackCapacity after state bound count := by
  have used := (effect.counts .instructions).2
  simp only [ChargeCounter.used,↓reduceIte] at used
  have limits := effect.limits
  rcases capacity with ⟨pc,codeCapacity,sourceCapacity,codeReserve,sourceReserve,_,instructions,operands,slots⟩
  refine ⟨by omega,by omega,by omega,by omega,by omega,coordinate,?_,operands,?_⟩
  · rw [limits]
    omega
  · rw [localsSame]
    exact slots

end Itasca.Runtime.Code
