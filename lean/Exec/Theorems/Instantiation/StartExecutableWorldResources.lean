import Exec.Theorems.Instantiation.StartEquation
import Exec.Theorems.Invocation.InvokeWorldResources
import Exec.Theorems.Invocation.InvokeHostWorldResources
import Exec.Platform.RecordingSpec
import Exec.Interp.Invocation.InvokeRecordingErasure
import Exec.Theorems.Invocation.InvokeWorld
import Exec.Theorems.Invocation.InvokeHostWorld
import Exec.Theorems.Api.ExecutableInv
import Exec.Theorems.Host.HostSegmentPublication
import Exec.Theorems.Composition.Certified.CertifiedExecutable
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
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

/-- The actual resolved start signature identifies either the original public
request or a request at a source-reachable evolving-world dispatch. -/
def WorldStartInvocationResourceCause {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (ambient : frame) (address : runtime.FuncAddr) (args : Slice runtime.Value)
    (after : runtime.store.Store M) (error : runtime.ExecError) : Prop :=
  ∃ function signature, store.funcs.val[address.index.val]?=some function ∧
    store.types.val[function.signature.val]?=some signature ∧
    signature.params.val=[] ∧ signature.results.val=[] ∧
    ((∃ ii fi, function.code=.Wasm ii fi ∧
      WorldDefinedSourceResourceCause
        memory hooks floats allocator view code (ExecutableInv view) store ambient
        address signature args after error) ∨
     ∃ identity, function.code=.Host identity ∧
      InitialHostSourceResourceCause hooks allocator store after identity signature error)

theorem invoke_start_executable_world_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (args : Slice runtime.Value) (empty : args.val = [])
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    runtime.interp.invoke_with memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value)
      ⦃ out => ∀ error, out.1=.Err error →
        WorldStartInvocationResourceCause memory hooks floats allocator view code exec store ambient address args out.2.2.1 error ⦄div := by
  have checked := Interp.typed_arguments_accepted memory store (Store.decodeStore view code store)
    args signature.params (by simp [ResultsTyped,params,empty]) (by simp [empty])
  cases kind : function.code with
  | Wasm instanceIndex functionIndex =>
    have recorded := invoke_defined_world_recorded_resources memory hooks floats allocator correct allocation interrupts
      view laws code (ExecutableInv view) (fun c s held=>held.toCertifiedApiStore.toCertifiedSupportedStore)
      (fun c before after held mutation=>held.update mutation) (fun c s held=>held.capacities)
      sound preserve externs issued exec store platform certified ambient ambientWf address function signature
      instanceIndex functionIndex args (alloc.vec.Vec.new runtime.Value) owner (by simp [empty]) hf hs kind checked
    apply WP.dspec_mono (Platform.Recording.erase_dspec _ _ _
      (Interp.recordedInvokeWith_erase memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value) []) recorded)
    rintro out ⟨events,actual,afterCode,fresh,kept,agrees,extension,success,failure⟩ error rejected
    exact ⟨function,signature,hf,hs,params,results,Or.inl ⟨instanceIndex,functionIndex,kind,(failure error rejected).2⟩⟩
  | Host identity =>
    have recorded := invoke_host_world_recorded_resources memory hooks floats allocator allocation interrupts view code
      (ExecutableInv view) (fun c s held=>held.shape) exec store platform certified certified.well_formed ambient ambientWf
      address function identity signature args (alloc.vec.Vec.new runtime.Value) owner hf kind hs (by simp [empty]) checked
      (fun p=>sound code store certified p identity) (preserve code store certified identity)
      (externs code store certified identity) (issued code store certified identity)
    apply WP.dspec_mono (Platform.Recording.erase_dspec _ _ _
      (Interp.recordedInvokeWith_erase memory hooks floats allocator exec store platform address args (alloc.vec.Vec.new runtime.Value) [])
      (WP.spec_dspec _ _ _ recorded))
    rintro out ⟨events,actual,afterCode,retained,success,failure⟩ error rejected
    exact ⟨function,signature,hf,hs,params,results,Or.inr ⟨identity,kind,(failure error rejected).2⟩⟩

theorem instantiate_start_executable_world_resources {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (platform : P)
    (certified : ExecutableInv view code store)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (identity : runtime.InstanceAddr) (address : runtime.FuncAddr)
    (function : runtime.store.FuncInst) (signature : Itasca.types.FuncType)
    (owner : address.store = store.id)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (params : signature.params.val = []) (results : signature.results.val = []) :
    Store.instantiate_start memory hooks floats allocator identity address store platform
      ⦃ out => ∀error,out.1=.Err error →
        WorldStartInvocationResourceCause memory hooks floats allocator view code startExecution store ambient address startArguments out.2.1 error ⦄div := by
  rw [start_equation]
  apply WP.dspec_bind (invoke_start_executable_world_resources memory hooks floats allocator correct allocation interrupts view laws code
    startExecution store platform certified sound preserve externs issued ambient ambientWf address function signature startArguments rfl owner hf hs params results)
  rintro ⟨status,execution,after,host,values⟩ causes
  cases status with
  | Ok unitValue =>
    apply WP.dspec.ret
    intro error impossible
    cases impossible
  | Err error =>
    apply WP.dspec.ret
    intro other same
    cases same
    exact causes error rfl
end Exec.Theorems
