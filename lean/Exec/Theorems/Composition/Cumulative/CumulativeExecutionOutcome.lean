import Exec.Interp.StructuredMachine.Advance
import Exec.Interp.StructuredMachine.OrdinaryExecution
import Exec.Interp.StructuredMachine.Execution
import Exec.Abs.Cumulative.Step
import Exec.Code.Local.Relations.Common.StatefulEmission
import Exec.Interp.Relations.SourceIndirectCallCause
import Exec.Interp.FloatCore.Outcome
import Exec.Theorems.Composition.Cumulative.CumulativeMutationCertified
namespace Itasca.Runtime.Theorems
open Aeneas Aeneas.Std Itasca.Runtime.Interp

def CumulativeTrap (trap : runtime.Trap) : Prop := FloatCoreTrap trap ∨ trap = .TableOutOfBounds ∨ trap = .UninitializedElement ∨ trap = .IndirectCallTypeMismatch

def CumulativeFailure {M P A : Type} (allocator : runtime.platform.Alloc A)
    (hooks : runtime.platform.Platform P M) (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (source : Abs.AState)
    (error : runtime.ExecError) : Prop :=
  ((∃ trap,error=.Trap trap ∧ CumulativeTrap trap) ∧ ∃ n,0<n ∧ Spec.StepsHN n (Abs.decode source) []
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
  {codeLength pc : Nat} {pending : Bool} {source : Abs.AState}
  {out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P}

end Itasca.Runtime.Theorems
