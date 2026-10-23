import Exec.Interp.Host.HostRecording
import Exec.Theorems.Host.HostCallSource

namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp

/-- The observable source endpoint for an isolated host call. A preparation
rejection has not consumed the call redex. -/
def hostCallResultConfig {M P : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (ambient : frame) (address : runtime.FuncAddr) (args : List val)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P) : config :=
  ⟨⟨Store.decodeStore view code out.2.2.1,ambient⟩,
    match out.1 with
    | .Ok _ => vals (out.2.1.host_results.val.map sourceValue)
    | .Err (.Trap .Host) | .Err (.Exhausted .CallStack) => [.TRAP]
    | _ => vals args ++ [.CALL_ADDR address.index.val]⟩

theorem HostCallSourceOutcome.events {M P : Type} (view : M → Slice U8)
    (code : Store.CodeInterpretation) (before : runtime.store.Store M) (ambient : frame)
    (address : runtime.FuncAddr) (args : List val) (base : Usize)
    (exec : runtime.interp.Execution)
    (out : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M × P)
    (observed : HostCallSourceOutcome view code before ambient address args base exec out) :
    StepsH ⟨⟨Store.decodeStore view code before,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
      (hostCallEvents address out) (hostCallResultConfig view code ambient address args out) := by
  obtain ⟨arguments,_,_,_,outcome⟩ := observed
  rcases outcome with ⟨success,_,source,_⟩ | ⟨error,source,_⟩
  · simpa only [hostCallEvents,hostCallResultConfig,success,arguments] using Spec.stepsH_single source
  · rcases error with trap | exhausted
    · simpa only [hostCallEvents,hostCallResultConfig,trap,arguments] using Spec.stepsH_single source
    · simpa only [hostCallEvents,hostCallResultConfig,exhausted,arguments] using Spec.stepsH_single source

/-- Exact event-list correspondence follows from the checked call theorem;
this adapter neither assumes a correctly typed host result nor changes the
underlying extracted computation. -/
theorem recorded_host_call_of_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (args : List val)
    (prior : List HostEvent)
    (initial : wf_config ⟨⟨Store.decodeStore view code store,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩)
    (source : runtime.interp.call memory hooks floats allocator exec store platform address base ⦃ out =>
      invariant out.2.2.1 ∧
      ((∃ error, out.1 = .Err error ∧ HostPreparationError error ∧ out.2.2.1 = store) ∨
        HostCallSourceOutcome view code store ambient address args base exec out) ⦄) :
    recordedHostCall memory hooks floats allocator exec store platform address base prior ⦃ (out,trace) =>
      invariant out.2.2.1 ∧ trace = prior ++ hostCallEvents address out ∧
      StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals args ++ [.CALL_ADDR address.index.val]⟩
        (hostCallEvents address out) (hostCallResultConfig view code ambient address args out) ⦄ := by
  unfold recordedHostCall Platform.Recording.run
  step with source as ⟨out,fresh,outcome⟩
  refine ⟨fresh,?_⟩
  rcases outcome with early | observed
  · obtain ⟨error,status,cause,unchanged⟩ := early
    cases error <;> simp only [HostPreparationError] at cause
    case Exhausted limit =>
      cases limit <;> simp only [HostPreparationError] at cause
      all_goals simpa only [hostCallEvents,hostCallResultConfig,status,unchanged] using StepsH.refl initial
    case Terminated =>
      simpa only [hostCallEvents,hostCallResultConfig,status,unchanged] using StepsH.refl initial
  · exact observed.events view code store ambient address args base exec out

/-- The fully discharged host-site theorem records exactly the event sequence
of its source execution, using the actual checked result buffers. -/
theorem recorded_host_call_source {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (code : Store.CodeInterpretation)
    (invariant : runtime.store.Store M → Prop)
    (shape : ∀ s, invariant s → Store.Shape view s)
    (sound : Platform.HostSound hooks invariant (Store.decodeStore view code))
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (valid : invariant store)
    (address : runtime.FuncAddr) (base : Usize) (ambient : frame) (wfAmbient : wf_frame ambient)
    (function : runtime.store.FuncInst) (identity : U64) (signature : Itasca.types.FuncType)
    (functionAt : store.funcs.val[address.index.val]? = some function)
    (host : function.code = .Host identity)
    (signatureAt : store.types.val[function.signature.val]? = some signature)
    (values : List val)
    (typed : signature.params.val.map sourceType = values.map Code.valueType)
    (arguments : ResultsTyped (Store.decodeStore view code store) (signature.params.val.map sourceType) values)
    (wellFormed : ∀ value ∈ values, wf_val value)
    (fits : ∀ value ∈ values, ResultIndexFits value)
    (represented : ValuesAt exec.slots.val base.val values)
    (issued : ∀ p args results answer,
      hooks.call_host p store identity args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (prior : List HostEvent) (sourceWf : wf_store (Store.decodeStore view code store)) :
    recordedHostCall memory hooks floats allocator exec store platform address base prior ⦃ (out,trace) =>
      invariant out.2.2.1 ∧ trace = prior ++ hostCallEvents address out ∧
      StepsH ⟨⟨Store.decodeStore view code store,ambient⟩,vals values ++ [.CALL_ADDR address.index.val]⟩
        (hostCallEvents address out) (hostCallResultConfig view code ambient address values out) ⦄ := by
  exact recorded_host_call_of_source memory hooks floats allocator view code invariant exec store platform
    address base ambient values prior (Spec.host_call_wf sourceWf wfAmbient arguments)
    (call_host_source memory hooks floats allocator allocation interrupts view code invariant shape sound
      exec store platform valid address base ambient wfAmbient function identity signature functionAt host
      signatureAt values typed arguments wellFormed fits represented issued)
end Exec.Theorems
