import Exec.Theorems.Progress.ExecutableEventfulFinite
import Exec.Theorems.Composition.Supported.SupportedEntry
import Exec.Theorems.Invocation.PublicExecutableEventfulInvocation
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- Every actual finite loop prefix after the public prepared defined call has
quantitative source progress from the invocation configuration. Entry simulation
is derived from that call, rather than supplied as a premise. -/
theorem call_defined_executable_eventful_finite_progress {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀p,hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (sound : Platform.HostSound hooks (ExecutableInv view code) (Store.decodeStore view code))
    (preserve : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → FrameStorePrefix store answer.2.2.1)
    (externs : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → store.externs.length≤answer.2.2.1.externs.length)
    (issuedResults : ∀store,ExecutableInv view code store → ∀host p args results answer,
      hooks.call_host p store host args results=.ok answer → ∀value∈answer.2.2.2.val,Store.IssuedValue answer.2.2.1 value)
    (prepared : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : ExecutableInv view code store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.FuncInst)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value)
    (empty : prepared.frames.val = []) (identity : prepared.store = store.id)
    (arguments : ValuesAt prepared.slots.val 0 (args.val.map sourceValue))
    (accepted : runtime.interp.check_values memory store args (alloc.vec.Vec.deref signature.params) = .ok (.Ok ()))
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex) :
    runtime.interp.call memory hooks floats allocator prepared store platform address 0#usize ⦃ out =>
      out.2.2.1 = store ∧ (out.1 = .Ok () → ∀dispatches last,
        ContinuingTrace (executionBody memory hooks floats allocator) dispatches
          (out.2.1,out.2.2.1,out.2.2.2,.Ok ()) last →
        ∃target events count, Spec.StepsHN count
          ⟨⟨Store.decodeStore view code store,ambient⟩,vals (args.val.map sourceValue)++[.CALL_ADDR address.index.val]⟩
          events target ∧ dispatches / (2 * U32.max + 3) ≤ count) ⦄ := by
  have certified := valid.toCertifiedApiStore.toCertifiedSupportedStore
  apply WP.spec_mono (call_defined_supported_entry memory hooks floats allocator allocation interrupts view code
    prepared store platform certified.shape certified.storeSyntax certified.segmentBounds certified.typed certified.supported certified.compiled
    ambient ambientWf address function signature instanceIndex functionIndex args empty identity arguments accepted owned hf hs hw)
  intro out result
  refine ⟨result.1,?_⟩
  intro success dispatches last trace
  obtain ⟨source,execution,sourceOwned,ambientEq,sourceStep⟩ := result.2 success
  let machine : EventfulMachine Interp.Executable.emission Abs.ExecutableInstr M P view code (signature.results.val.map sourceType) :=
    ⟨store,out.2.1,out.2.2.2,source,0,false,execution,certified,sourceOwned⟩
  have actual : ContinuingTrace (executionBody memory hooks floats allocator) dispatches
      (machine.exec,machine.store,machine.platform,.Ok ()) last := by
    simpa only [machine,result.1] using trace
  obtain ⟨target,events,count,steps,bound⟩ := executable_eventful_finite_progress memory hooks floats allocator
    correct allocation interrupts view laws code sound preserve externs issuedResults dispatches machine valid last actual
  exact ⟨Abs.decode target,events,count+1,by simpa using Spec.StepsHN.cons sourceStep steps,by omega⟩

end Exec.Theorems
