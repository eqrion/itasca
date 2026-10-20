import Exec.Code.Module.CompileEntry

namespace Exec.Code
open Aeneas Aeneas.Std

/-- Published source slots form a dense prefix; all later slots remain vacant. -/
structure FunctionSlotPrefix (count cursor : Nat)
    (functions : List (Option runtime.bytecode.CompiledFunction)) : Prop where
  length : functions.length = count
  inside : cursor ≤ count
  filled : ∀ index, index < cursor → ∃ function, functions[index]? = some (some function)
  vacant : ∀ index, cursor ≤ index → index < count → functions[index]? = some none

/-- Publishing exactly the next source slot extends the prefix once. -/
theorem FunctionSlotPrefix.publish {count cursor functions}
    (held : FunctionSlotPrefix count cursor functions) (remaining : cursor < count)
    (function : runtime.bytecode.CompiledFunction) :
    FunctionSlotPrefix count (cursor+1) (functions.set cursor (some function)) := by
  refine ⟨by simpa only [List.length_set] using held.length,by omega,?_,?_⟩
  · intro index bound
    by_cases same : index = cursor
    · subst index
      exact ⟨function,by simp [List.getElem?_set_self,held.length,remaining]⟩
    · obtain ⟨previous,found⟩ := held.filled index (by omega)
      exact ⟨previous,by rw [List.getElem?_set_ne (by omega)]; exact found⟩
  · intro index lower upper
    rw [List.getElem?_set_ne (by omega)]
    exact held.vacant index (by omega) upper

end Exec.Code
