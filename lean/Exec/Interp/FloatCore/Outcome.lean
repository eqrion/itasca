import Exec.Interp.FloatCore.Advance
import Exec.Interp.Core.Outcome
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Scalar Core traps are precise source failures, not arbitrary runtime errors. -/
def FloatCoreTrap (trap : runtime.Trap) : Prop :=
  trap = .Unreachable ∨ trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow ∨ trap = .MemoryOutOfBounds ∨ trap = .InvalidConversionToInteger

def FloatCoreFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : Abs.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap, error = .Trap trap ∧ FloatCoreTrap trap) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode source) []
    ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩) ∨
  (error = .Terminated ∧ ∃ after, hooks.interrupt platform = .ok (.Terminate,after)) ∨
  ∃ index raw inst compiled,
    index.val+1 = exec.frames.length ∧ exec.frames.val[index.val]? = some raw ∧
    store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error

/-- Every normally returned scalar dispatch retains its concrete mutation and
advances the source machine or exhibits a precise failure cause. -/
def FloatCoreOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : Abs.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CoreStoreMutation view source store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => FloatCoreAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => FloatCoreFailure allocator hooks exec store platform source error ∧
      Store.decodeStore view code out.2.2.1 = source.store

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem FloatCoreOutcome.success (mutation : CoreStoreMutation view source store out.2.2.1)
    (status : out.1 = .Ok ())
    (advance : FloatCoreAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    FloatCoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  exact ⟨mutation,by simpa only [status] using advance⟩

theorem FloatCoreOutcome.unchanged_success (same : out.2.2.1 = store) (status : out.1 = .Ok ())
    (advance : FloatCoreAdvance view code store out.2.1 expected codeLength pc pending source) :
    FloatCoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply FloatCoreOutcome.success (by rw [same]; exact .unchanged) status
  simpa only [same] using advance

theorem FloatCoreOutcome.failure (mutation : CoreStoreMutation view source store out.2.2.1)
    {error : runtime.ExecError} (status : out.1 = .Err error)
    (decoded : Store.decodeStore view code out.2.2.1 = source.store)
    (cause : FloatCoreFailure allocator hooks exec store platform source error) :
    FloatCoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  exact ⟨mutation,by simpa only [status] using And.intro cause decoded⟩

end Exec.Interp
