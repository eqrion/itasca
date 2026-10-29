import Itasca.Runtime.Integration.Api.ExecutableInv
import Itasca.Runtime.Integration.Execution.Resources.InvocationErrors
import Itasca.Runtime.Spec.Invocation
import Itasca.Runtime.Interp.Relations.FrameStorePrefix
import Itasca.Runtime.Interp.Relations.ArgumentRejectionKind

/-! Shared public invocation outcomes and erasure. These predicates retain a
single final code interpretation and sit below the public API constructions. -/
namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

/-- The public entry checks that reject a call before any state changes: a handle from
another store, or arguments that fail the callee signature check. -/
def InvocationRejected {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (error : runtime.ExecError) : Prop :=
  (address.store≠store.id ∧ error=.WrongStore) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params)=.ok (.Err error)

theorem InvocationRejected.kind {M : Type} {memory : runtime.platform.MemoryBuffer M}
    {store : runtime.store.Store M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {error : runtime.ExecError} (rejected : InvocationRejected memory store address args error) :
    error=.BadArguments ∨ error=.WrongStore := by
  rcases rejected with ⟨_,rfl⟩ | ⟨function,signature,_,_,checked⟩
  · exact Or.inr rfl
  · exact check_values_error_kind memory store args _ error checked

/-- Public source correspondence at the exact concrete log, allowing callbacks
to publish new code while preserving existing issued instances. -/
def ExecutableWorldRecordedOutcome {M P : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : Store.CodeInterpretation) (before : runtime.store.Store M)
    (exec : runtime.interp.Execution) (platform : P) (address : runtime.FuncAddr)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (initial : config)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution ×
      runtime.store.Store M × P × alloc.vec.Vec runtime.Value) (events : List HostEvent) : Prop :=
  ∃ afterCode, Store.CodeAgreesOn before code afterCode ∧
  ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
  Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1) ∧
  (∃body,StepsH initial events ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,body⟩) ∧
  (out.1=.Ok () → (StepsH initial events
    ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
    (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value)) ∧
  (∀error,out.1=.Err error →
    (InvocationRejected memory before address args error ∧ out=(.Err error,exec,before,platform,results) ∧ events=[]) ∨
    EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error)

theorem ExecutableWorldRecordedOutcome.of_executed {M P : Type}
    {memory : runtime.platform.MemoryBuffer M} {address : runtime.FuncAddr} {args : Slice runtime.Value}
    {view : M → Slice U8} {code afterCode : Store.CodeInterpretation} {before : runtime.store.Store M}
    {exec : runtime.interp.Execution} {platform : P} {results : alloc.vec.Vec runtime.Value}
    {initial : config} {out} {events : List HostEvent}
    (agrees : Store.CodeAgreesOn before code afterCode)
    (retained : ExecutableInv view afterCode out.2.2.1 ∧ FrameStorePrefix before out.2.2.1 ∧
      Extend_store (Store.decodeStore view code before) (Store.decodeStore view afterCode out.2.2.1))
    (success : out.1=.Ok () → (StepsH initial events
      ⟨⟨Store.decodeStore view afterCode out.2.2.1,Spec.invocationFrame⟩,vals (out.2.2.2.2.val.map sourceValue)⟩) ∧
      (∀value∈out.2.2.2.2.val,Store.ValueInStore out.2.2.1 value))
    (failure : ∀error,out.1=.Err error →
      EventfulInvocationError initial events (Store.decodeStore view afterCode out.2.2.1) Spec.invocationFrame error) :
    ExecutableWorldRecordedOutcome memory view code before exec platform address args results initial out events := by
  refine ⟨afterCode,agrees,retained.1,retained.2.1,retained.2.2,?_,success,fun error failed=>Or.inr (failure error failed)⟩
  cases status : out.1 with
  | Ok value =>
    cases value
    exact ⟨_,(success status).1⟩
  | Err error =>
    have outcome := failure error status
    obtain ⟨body,steps⟩ := outcome.reachable
    exact ⟨body,steps⟩

end Itasca.Runtime.Integration
