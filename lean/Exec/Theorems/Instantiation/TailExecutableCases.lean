import Exec.Theorems.Composition.Certified.CertifiedExecutable
import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Invocation.InvokeSupported
import Exec.Theorems.Composition.Entry
import Exec.Code.Local.Relations.Common.Function
import Exec.Interp.Calls.CallRefinement
import Exec.Interp.Control.StructuredPoint
import Exec.Interp.Calls.CallStack
import Exec.Interp.Machines.Slice.SliceExecution
import Exec.Interp.Machines.Slice.SliceHistory
import Exec.Interp.Relations.Readback
import Exec.Abs.Results
import Exec.Interp.Invocation.InvokeCompose
import Exec.Interp.Invocation.InvokeChecks
import Exec.Interp.Relations.Marshal
import Exec.Representation.Collection
import Exec.Interp.Relations.TypeSlots
import Exec.Interp.Relations.Ensure
import Exec.Interp.Relations.ExecutionLoop
import Exec.Interp.Machines.Slice.SliceErrors
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Machines.Slice.SliceDivergence
import Exec.Interp.Relations.TypedArguments
import Exec.Spec.Invocation
import Exec.Store.Invariant.Typing
import Exec.Store.Instantiation.InstantiateStart
import Exec.Theorems.Instantiation.StartAmbient
import Exec.Theorems.Instantiation.StartResolution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

def TailExecutableSourceResult {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (inst : runtime.store.ModuleInst) (store after : runtime.store.Store M) (identity : runtime.InstanceAddr)
    (initialized : core.result.Result Unit runtime.ExecError)
    (result : core.result.Result runtime.InstanceAddr runtime.ExecError) : Prop :=
  match initialized with
  | .Err error => result = .Err error
  | .Ok _ =>
    (inst.module.module.env.start = none ∧ result = .Ok identity) ∨
    ∃ index address, inst.module.module.env.start = some index ∧
      inst.funcs.val[index.val]? = some address ∧
      (∀ returned, result = .Ok returned → returned = identity ∧
        StepsH (moduleStartConfiguration view code store inst index) []
          ⟨⟨Store.decodeStore view code after, moduleStartFrame store inst⟩, []⟩) ∧
      (∀ error, result = .Err error → SupportedInvocationError
        (moduleStartConfiguration view code store inst index)
        (Store.decodeStore view code after) (moduleStartFrame store inst) error)

end Exec.Theorems
