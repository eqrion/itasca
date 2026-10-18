import Exec.Theorems.Api.InvocationObjectExclusion
import Exec.Theorems.Invocation.PublicEventfulInvocationCauses
import Exec.Theorems.Composition.DefinedEventfulSourceResources
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

def InitialHostSourceResourceCause {M P A : Type}
    (hooks : runtime.platform.Platform P M) (allocator : runtime.platform.Alloc A)
    (store after : runtime.store.Store M) (identity : U64) (signature : Itasca.types.FuncType) : runtime.ExecError → Prop
  | .Exhausted .Values => store.limits.max_values.val<signatureWords (Store.decodeFuncType signature)
  | .Exhausted .Allocation => HostSignatureAllocation allocator (signature.params.val.map sourceType) (signature.results.val.map sourceType) 0
  | .Exhausted .CallStack => ∃ p args defaults host returned,
      hooks.call_host p store identity args defaults=.ok (.Err .StackOverflow,host,after,returned)
  | .Terminated => ∃ before after,hooks.interrupt before=.ok (.Terminate,after)
  | .Exhausted .Objects => False
  | _ => True

/-- Public resource bounds are expressed by source signatures and canonical
source function capacities. An executed body retains its actual reached
history and current store limits after any intervening host callbacks. -/
def ExecutableInvocationSourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ((error=.BadArguments ∨ error=.WrongStore) ∧ after=store) ∨
  ∃ function signature,store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    ((∃ ii fi,function.code=.Wasm ii fi ∧
      (CanonicalInvocationResourceCause allocator hooks
        ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
        (Store.decodeStore view code store) (Store.decodeFuncType signature) address.index.val
        store.limits.max_values.val store.limits.max_frames.val error ∨
       ReachedEventfulResourceCause (emission:=Executable.emission) (allowed:=Abs.ExecutableInstr)
        memory hooks floats allocator view code (signature.results.val.map sourceType) (ExecutableInv view code) store
        ⟨⟨Store.decodeStore view code store,Spec.invocationFrame⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩ after error)) ∨
     ∃ identity,function.code=.Host identity ∧ InitialHostSourceResourceCause hooks allocator store after identity signature error)

theorem ExecutableEventfulInvocationCause.source_resources {M P F A : Type}
    {memory : runtime.platform.MemoryBuffer M} {hooks : runtime.platform.Platform P M}
    {floats : runtime.platform.FloatOps F} {allocator : runtime.platform.Alloc A}
    {view : M → Slice U8} {code : Store.CodeInterpretation}
    {exec : runtime.interp.Execution} {store : runtime.store.Store M}
    {address : runtime.FuncAddr} {args : Slice runtime.Value} {results : alloc.vec.Vec runtime.Value}
    {after : runtime.store.Store M} {error : runtime.ExecError}
    (valid : ExecutableInv view code store)
    (cause : ExecutableEventfulInvocationCause memory hooks floats allocator view code exec store address args results after error) :
    ExecutableInvocationSourceCause memory hooks floats allocator view code store address args after error := by
  rcases cause with rejected | ⟨function,signature,hf,hs,defined | host⟩
  · exact Or.inl rejected
  · obtain ⟨ii,fi,kind,cause⟩ := defined
    refine Or.inr ⟨function,signature,hf,hs,Or.inl ⟨ii,fi,kind,?_⟩⟩
    exact cause.source_resources (fun _ held=>held.capacities) valid valid.typed function hf kind
  · obtain ⟨identity,kind,cause⟩ := host
    refine Or.inr ⟨function,signature,hf,hs,Or.inr ⟨identity,kind,?_⟩⟩
    cases error with
    | Terminated => exact cause.interrupted
    | Exhausted reason =>
      cases reason with
      | Values => exact cause.source_values
      | Allocation => exact cause.source_allocation
      | CallStack => exact cause.host_overflow
      | Objects => exact cause.no_objects
    | _ => trivial
end Exec.Theorems
