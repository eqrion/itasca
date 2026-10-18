import Exec.Theorems.Invocation.InvokeFloatCore
import Exec.Theorems.Progress.FloatCoreDivergence
import Exec.Interp.Invocation.InvokeDivergence
import Exec.Interp.Invocation.InvokeMutableDivergence
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem invoke_float_core_divergent_machine {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedFloatCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div) :
    ∃ machine : FloatCoreMachine M P view code (signature.results.val.map Interp.sourceType),
      StepH ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (Abs.decode machine.source) ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator machine.exec machine.store machine.platform (.Ok ()) = .div := by
  let entry (prepared : runtime.interp.Execution) : Prop := ∃ source,
    Interp.FloatCoreExecution view code store prepared source (signature.results.val.map Interp.sourceType) 0 false ∧
    Abs.Ownership.CoreOwned (Store.ownershipBounds store) source ∧ source.ambient = ambient ∧
    StepH ⟨⟨Store.decodeStore view code store,ambient⟩,
      vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] (Abs.decode source)
  have accepted := Interp.invoke_divergent_arguments memory hooks floats allocator exec store platform address
    function signature args results owner hf hs divergent
  have reached : ∃ prepared p, entry prepared ∧
      runtime.interp.invoke_with_loop2 memory hooks floats allocator prepared store p (.Ok ()) = .div := by
    apply Interp.invoke_mutable_divergent_entry memory hooks floats allocator allocation exec store platform address
      function signature args results owner hf hs accepted (fun value member => (owned value member).1) entry ?_ ?_ divergent
    · intro prepared p identity empty arguments
      exact call_defined_float_core_entry_certified memory hooks floats allocator allocation interrupts view code
        prepared store p certified ambient ambientWf address function signature instanceIndex functionIndex args
        empty identity arguments accepted owned hf hs hw
    · intro prepared p entered
      obtain ⟨source,invariant,ownedSource,ambientEq,sourceStep⟩ := entered
      let machine : FloatCoreMachine M P view code (signature.results.val.map Interp.sourceType) :=
        ⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩
      apply WP.dspec_mono (float_core_loop memory hooks floats allocator correct allocation interrupts view laws code machine)
      intro out outcome
      obtain ⟨fresh,metadata,extension,readback⟩ := outcome.readback
      exact ⟨metadata.identity,metadata.functions,metadata.types,fun ok => by
        obtain ⟨values,tags,wf,fits,represented,steps⟩ := readback ok
        exact ⟨values,tags,wf,fits,represented⟩⟩
  obtain ⟨prepared,p,⟨source,invariant,ownedSource,ambientEq,sourceStep⟩,bodyDivergent⟩ := reached
  exact ⟨⟨store,prepared,p,source,0,false,invariant,certified,ownedSource,hostFree⟩,sourceStep,bodyDivergent⟩

theorem invoke_defined_float_core_no_silent_divergence {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedFloatCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div)
    (requested : Nat) :
    ∃ final count, Spec.StepsHN count
      ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ [] final ∧ requested ≤ count := by
  obtain ⟨machine,entry,bodyDivergent⟩ := invoke_float_core_divergent_machine memory hooks floats allocator correct allocation interrupts view laws code exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex args results owner owned hf hs hw divergent
  obtain ⟨final,count,history,steps,cost⟩ := float_core_no_silent_divergence memory hooks floats allocator correct allocation interrupts view laws code machine bodyDivergent requested
  exact ⟨Abs.decode final.source,count+1,by simpa using Spec.StepsHN.cons entry steps,by omega⟩

theorem invoke_defined_float_core_infinite_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedFloatCoreStore view code store) (hostFree : CoreHostFree store)
    (ambient : frame) (ambientWf : wf_frame ambient)
    (address : runtime.FuncAddr) (function : runtime.store.Function)
    (signature : Itasca.types.FuncType) (instanceIndex functionIndex : Usize)
    (args : Slice runtime.Value) (results : alloc.vec.Vec runtime.Value)
    (owner : address.store = store.id)
    (owned : ∀ value ∈ args.val, Store.ValueInStore store value)
    (hf : store.funcs.val[address.index.val]? = some function)
    (hs : store.types.val[function.signature.val]? = some signature)
    (hw : function.code = .Wasm instanceIndex functionIndex)
    (divergent : runtime.interp.invoke_with memory hooks floats allocator exec store platform address args results = .div) :
    ∃ states : Nat → config,
      states 0 = ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ ∧
      ∀ n, ∃ count, 0 < count ∧ Spec.StepsHN count (states n) [] (states (n+1)) := by
  obtain ⟨machine,entry,bodyDivergent⟩ := invoke_float_core_divergent_machine memory hooks floats allocator correct allocation interrupts view laws code exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex args results owner owned hf hs hw divergent
  obtain ⟨states,initial,steps⟩ := float_core_infinite_source memory hooks floats allocator correct allocation interrupts view laws code machine bodyDivergent
  refine ⟨fun n => match n with | 0 => _ | n+1 => states n,rfl,?_⟩
  intro n
  cases n with
  | zero => exact ⟨1,by omega,by simpa only [initial,List.nil_append,Nat.zero_add] using Spec.StepsHN.cons entry (.refl machine.invariant.typed.typed.decode_wf)⟩
  | succ n => exact steps n

end Exec.Theorems
