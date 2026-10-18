import Exec.Theorems.Instantiation.InstantiateSourceOrigin
import Exec.Theorems.Composition.InstantiationResult
import Exec.Store.Initialization.SegmentInitializeSource
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Segment effects and the optional actual start compose into the complete
source execution from the generated instantiation configuration. -/
theorem instantiate_tail_execution {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : CodeInterpretation) (certified : CertifiedSliceStore view code store)
    (imports : InitializerImports store inst) (types : SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map decodeFuncType))
    (raw : ModuleBinary.Module)
    (matched : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw)
    (initialWf : wf_config (sourceInstantiationConfiguration view code store inst raw)) :
    instantiate_tail memory hooks floats allocator identity store platform
      ⦃ out => out.2.2.2 = true ∧ CertifiedSliceStore view code out.2.1 ∧
        SegmentObjectMetadata view store out.2.1 ∧
        (∀ address, out.1 = .Ok address → address = identity) ∧
        InstantiationExecution (sourceInstantiationConfiguration view code store inst raw)
          (decodeStore view code out.2.1) (moduleStartFrame out.2.1 inst) out.1 ⦄div := by
  let continuation := (inst.module.module.env.start.map (fun index => admininstr.CALL (.mk_uN index.val))).toList
  have continuationWf : Forall wf_admininstr continuation := by
    cases hs : inst.module.module.env.start with
    | none => simp [continuation,hs,Forall]
    | some index =>
      have indexWf : wf_uN 32 (.mk_uN index.val) := by constructor; scalar_tac
      simpa [continuation,hs,Forall] using wf_admininstr.admininstr_case_10 (.mk_uN index.val) indexWf
  have startEq : raw.start = inst.module.module.env.start := congrArg ModuleBinary.Module.start matched.1
  have initSource := initialize_segments_raw_source memory hooks floats allocator view laws law store platform identity.index
    inst bytes profile limits accepted found code certified.shape certified.storeSyntax certified.segmentBounds
    imports (certified.shape.initializer_bindings (List.mem_of_getElem? found)) types
    (moduleStartFrame store inst) (moduleStartFrame_wf code store identity.index inst certified.storeSyntax found)
    rfl raw matched continuation continuationWf
  have tail := instantiate_tail_slice memory hooks floats allocator view laws law interrupts store platform identity
    inst bytes profile limits accepted found code certified imports types table
  apply WP.dspec_mono tail
  rintro ⟨result,after,host,committed⟩ ⟨commit,afterCertified,extension,metadata,returned,status,initRun,outcome⟩
  dsimp only at commit afterCertified metadata initRun outcome ⊢
  refine ⟨commit,afterCertified,metadata,returned,?_⟩
  rw [initRun,WP.spec_ok] at initSource
  dsimp only at initSource
  have frameEq : moduleStartFrame store inst = moduleStartFrame after inst := by
    simp only [moduleStartFrame,decodeInstance,metadata.space.signatures]
  have sourceEq : (⟨⟨decodeStore view code store,moduleStartFrame store inst⟩,
      segmentRawSource raw ++ continuation⟩ : config) = sourceInstantiationConfiguration view code store inst raw := by
    simp only [sourceInstantiationConfiguration,segmentRawSource,continuation,startEq,moduleStartFrame,List.append_assoc]
  rcases initSource with ⟨reason,statusEq,unchanged⟩ | ⟨classified,reduced⟩
  · subst status
    change result = .Err (.Exhausted reason) at outcome
    subst result
    subst after
    exact ⟨moduleStartFrame store inst,_,StepsH.refl initialWf⟩
  · rw [sourceEq,frameEq] at reduced
    cases status with
    | Ok value =>
      cases value
      apply outcome.initialized_execution
      exact reduced
    | Err error =>
      change result = .Err error at outcome
      subst result
      change error = .Trap .MemoryOutOfBounds ∨ error = .Trap .TableOutOfBounds at classified
      rcases classified with rfl | rfl <;> exact reduced
end Exec.Theorems
