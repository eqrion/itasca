import Exec.Interp.Core.Advance
import Exec.Interp.Core.Mutation
import Exec.Interp.Relations.SourceCallCause
namespace Exec.Interp
open Aeneas Aeneas.Std

/-- Scalar Core traps are precise source failures, not arbitrary runtime errors. -/
def CoreTrap (trap : runtime.Trap) : Prop :=
  trap = .Unreachable ∨ trap = .IntegerDivideByZero ∨ trap = .IntegerOverflow ∨ trap = .MemoryOutOfBounds

/-- A host entry is an explicit boundary until a host-soundness contract is
attached to the mutable execution loop. -/
def CoreHostBoundary {M : Type} (exec : runtime.interp.Execution) (store : runtime.store.Store M) : Prop :=
  ∃ (frameIndex : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction) (index offset : U32) (address : runtime.FuncAddr)
    (function : runtime.store.Function), ∃ host,
    frameIndex.val+1 = exec.frames.length ∧ exec.frames.val[frameIndex.val]? = some raw ∧
    store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    compiled.code.val[raw.pc.val]? = some (.Call index offset) ∧
    inst.funcs.val[index.val]? = some address ∧
    store.funcs.val[address.index.val]? = some function ∧ function.code = .Host host

def CoreFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : Abs.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap, error = .Trap trap ∧ CoreTrap trap) ∧ ∃ n, 0 < n ∧ Spec.StepsHN n (Abs.decode source) []
    ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩) ∨
  (error = .Terminated ∧ ∃ after, hooks.interrupt platform = .ok (.Terminate,after)) ∨
  ∃ index raw inst compiled,
    index.val+1 = exec.frames.length ∧ exec.frames.val[index.val]? = some raw ∧
    store.instances.val[raw.instance.val]? = some inst ∧
    inst.module.functions.val[raw.function.val]? = some compiled ∧
    SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error

/-- Every normally returned scalar dispatch retains its concrete mutation and
advances the source machine or exhibits a precise failure cause. -/
def CoreOutcome {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (expected : List valtype) (codeLength pc : Nat) (pending : Bool) (source : Abs.AState)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : Prop :=
  CoreStoreMutation view source store out.2.2.1 ∧
    match out.1 with
    | .Ok _ => CoreAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source
    | .Err error => CoreFailure allocator hooks exec store platform source error ∧
      Store.decodeStore view code out.2.2.1 = source.store

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

theorem CoreOutcome.success (mutation : CoreStoreMutation view source store out.2.2.1)
    (status : out.1 = .Ok ())
    (advance : CoreAdvance view code out.2.2.1 out.2.1 expected codeLength pc pending source) :
    CoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  exact ⟨mutation,by simpa only [status] using advance⟩

theorem CoreOutcome.unchanged_success (same : out.2.2.1 = store) (status : out.1 = .Ok ())
    (advance : CoreAdvance view code store out.2.1 expected codeLength pc pending source) :
    CoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  apply CoreOutcome.success (by rw [same]; exact .unchanged) status
  simpa only [same] using advance

theorem CoreOutcome.failure (mutation : CoreStoreMutation view source store out.2.2.1)
    {error : runtime.ExecError} (status : out.1 = .Err error)
    (decoded : Store.decodeStore view code out.2.2.1 = source.store)
    (cause : CoreFailure allocator hooks exec store platform source error) :
    CoreOutcome allocator hooks view code exec store platform expected codeLength pc pending source out := by
  exact ⟨mutation,by simpa only [status] using And.intro cause decoded⟩

end Exec.Interp
