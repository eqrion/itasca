import Itasca.Runtime.Interp.Machine.Progress.Advance
import Itasca.Runtime.Interp.Machine.Progress.OrdinaryExecution
import Itasca.Runtime.Interp.Machine.Execution
import Itasca.Runtime.SourceMachine.Cumulative.Step
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulEmission
import Itasca.Runtime.Interp.Relations.SourceIndirectCallCause
import Itasca.Runtime.Interp.Machine.Outcomes.ScalarTraps
import Itasca.Runtime.Integration.Execution.Mutation.Certificate
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp

def CumulativeTrap (trap : runtime.Trap) : Prop := FloatCoreTrap trap ∨ trap = .TableOutOfBounds ∨ trap = .UninitializedElement ∨ trap = .IndirectCallTypeMismatch

def CumulativeFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : SourceMachine.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap,error=.Trap trap ∧ CumulativeTrap trap) ∧ ∃ n,0<n ∧ Spec.StepsHN n (SourceMachine.decode source) []
    ⟨⟨source.store,source.ambient⟩,[.TRAP]⟩) ∨
  (error=.Terminated ∧ ∃ after,hooks.interrupt platform=.ok (.Terminate,after)) ∨
  ∃ index raw inst compiled,
    index.val+1=exec.frames.length ∧ exec.frames.val[index.val]?=some raw ∧
    store.instances.val[raw.instance.val]?=some inst ∧ inst.module.functions.val[raw.function.val]?=some compiled ∧
    (SourceDirectCallCause allocator hooks exec store platform index raw inst compiled source error ∨
      ∃ code, SourceIndirectCallCause allocator hooks code exec store platform index raw compiled source error)

variable {M P A : Type} {allocator : runtime.platform.Alloc A} {hooks : runtime.platform.Platform P M}
  {view : M → Slice U8} {code : Store.CodeInterpretation} {exec : runtime.interp.Execution}
  {store : runtime.store.Store M} {platform : P} {expected : List valtype}
  {codeLength pc : Nat} {pending : Bool} {source : SourceMachine.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

end Itasca.Runtime.Integration
