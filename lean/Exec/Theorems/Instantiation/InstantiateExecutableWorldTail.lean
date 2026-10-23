import Exec.Theorems.Instantiation.InstantiateExecutableWorldRecordedTail
import Exec.Store.Instantiation.InstantiateRecordingErasure

/-! Ordinary instantiation-tail correspondence erases the recorded construction.
The no-link client uses this projection with the same source and final code world. -/
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Segment effects and the optional actual start compose into the complete
source execution from the generated instantiation configuration. -/
theorem instantiate_tail_executable_world_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.ModuleInst) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : CodeInterpretation) (certified : ExecutableInv view code store)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ c store, ExecutableInv view c store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => ∃ afterCode, CodeAgreesOn store code afterCode ∧ out.2.2.2 = true ∧ ExecutableInv view afterCode out.2.1 ∧
        Extend_store (decodeStore view code store) (decodeStore view afterCode out.2.1) ∧
        Interp.FrameStorePrefix store out.2.1 ∧ SegmentPublication store out.2.1 ∧
        (∀ address, out.1 = .Ok address → address = identity) ∧
        (∃ events, EventfulInstantiationExecution (sourceInstantiationConfiguration view code store inst raw)
          events (decodeStore view afterCode out.2.1) (moduleStartFrame out.2.1 inst) out.1) ⦄div := by
  have recorded := instantiate_tail_executable_world_recorded_execution memory hooks floats allocator
    view laws correct law interrupts store platform identity inst bytes profile limits accepted found code certified
    sound preserve externs issued imports types table raw matched initialWf
  have actual := Platform.Recording.erase_dspec _ _ _
    (recordedInstantiateTail_erase memory hooks floats allocator identity store platform []) recorded
  apply WP.dspec_mono actual
  intro out post
  obtain ⟨events,recorded,afterCode,agrees,committed,valid,extension,retained,publication,success,execution⟩ := post
  exact ⟨afterCode,agrees,committed,valid,extension,retained,publication,success,events,execution⟩
end Exec.Theorems
