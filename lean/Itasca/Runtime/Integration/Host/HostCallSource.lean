import Itasca.Runtime.Interp.Control.StructuredPoint
import Itasca.Runtime.Interp.Host.HostPreparationCauses
import Itasca.Runtime.Store.Invariant.CheckedValues
import Itasca.Runtime.Spec.HostCall
import Itasca.Runtime.Interp.Host.HostResume
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Generated.Types
import Itasca.Runtime.Spec.Extend

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- Observable behavior after an actual host callback. Preparation rejections
are separated by the calling theorem because they perform no host event. -/
def HostCallSourceOutcome {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (before : runtime.store.Store M) (ambient : frame) (address : runtime.FuncAddr)
    (args : List val) (base : Usize) (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  out.2.1.host_args.val.map sourceValue = args ∧ out.2.1.frames = exec.frames ∧ out.2.1.store = exec.store ∧
  exec.slots.length ≤ out.2.1.slots.length ∧
  ((out.1 = .Ok () ∧
    ValuesAt out.2.1.slots.val base.val (out.2.1.host_results.val.map sourceValue) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args (some (out.2.1.host_results.val.map sourceValue))]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,vals (out.2.1.host_results.val.map sourceValue)⟩ ∧
    (∀ j, j < exec.slots.length →
      j < base.val ∨ base.val + Compiler.slots (out.2.1.host_results.val.map (Compiler.valueType ∘ sourceValue)) ≤ j →
      out.2.1.slots.val[j]? = exec.slots.val[j]?)) ∨
   ((out.1 = .Err (.Trap .Host) ∨ out.1 = .Err (.Exhausted .CallStack)) ∧
    StepH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      [.call address.index.val args none]
      ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,[.TRAP]⟩ ∧
    (∀ j, j < exec.slots.length → out.2.1.slots.val[j]? = exec.slots.val[j]?)))

/-- Actual resource causes for a host call, including a callback's explicit
stack-overflow reply. The checked callback equation retains its returned store. -/
def HostCallCauses {A M P : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (signature : Itasca.types.FuncType)
    (base : Usize) (identity : U64)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  match out.1 with
  | .Ok _ | .Err (.Trap _) => True
  | .Err (.Exhausted .CallStack) =>
      ∃ p args defaults returned, hooks.call_host p store identity args defaults =
        .ok (.Err .StackOverflow,out.2.2.2,out.2.2.1,returned)
  | .Err error => HostPreparationCause allocator hooks exec store platform signature base error

theorem HostCallCauses.of_preparation {A M P : Type} {allocator : runtime.platform.Alloc A}
    {hooks : runtime.platform.Platform P M} {exec : runtime.interp.Execution}
    {store : runtime.store.Store M} {platform : P} {signature : Itasca.types.FuncType}
    {base : Usize} {identity : U64}
    {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}
    {error : runtime.ExecError} (status : out.1 = .Err error)
    (cause : HostPreparationCause allocator hooks exec store platform signature base error) :
    HostCallCauses allocator hooks exec store platform signature base identity out := by
  simp only [HostCallCauses,status]
  cases error <;> simp_all [HostPreparationCause]
  rename_i limit
  cases limit <;> simp_all [HostPreparationCause]

end Itasca.Runtime.Integration
