import Exec.Theorems.Host.HostCallSource
import Exec.Interp.Relations.FrameStorePrefix
import Exec.Theorems.Host.Chosen.HostResumeChosen
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

def ChosenHostCallSourceOutcome (choices : Spec.SourceChoices) (occurrence : Nat) {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (args : List val) (base : Usize) (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.1.host_args.val.map sourceValue = args ∧ out.2.1.frames = exec.frames ∧ out.2.1.store = exec.store ∧
  exec.slots.length ≤ out.2.1.slots.length ∧
  ((out.1 = .Ok () ∧
    ValuesAt out.2.1.slots.val base.val (out.2.1.host_results.val.map sourceValue) ∧
    Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args (some (out.2.1.host_results.val.map sourceValue))]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.1.host_results.val.map sourceValue)⟩ ∧
    (∀ j, j < exec.slots.length →
      j < base.val ∨ base.val + Code.slots (out.2.1.host_results.val.map (Code.valueType ∘ sourceValue)) ≤ j →
      out.2.1.slots.val[j]? = exec.slots.val[j]?)) ∨
   ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack)) ∧
    Spec.ChoiceStep choices occurrence ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args none]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩ ∧
    (∀ j, j < exec.slots.length → out.2.1.slots.val[j]? = exec.slots.val[j]?)))

end Exec.Theorems
