import Exec.Theorems.Instantiation.StartExecutableWorldInfinite
import Exec.Theorems.Instantiation.TailExecutableCases
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt

theorem instantiate_tail_executable_world_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (store : runtime.store.Store M) (platform : P) (identity : runtime.InstanceAddr)
    (inst : runtime.store.Instance) (bytes : Slice U8) (profile : Itasca.ValidationProfile)
    (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module))
    (found : store.instances.val[identity.index.val]? = some inst)
    (code : Store.CodeInterpretation) (certified : ExecutableInv view code store)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ code store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ code store, ExecutableInv view code store → ∀ host p args results answer,
      hooks.call_host p store host args results = .ok answer → ∀ value ∈ answer.2.2.2.val, Store.IssuedValue answer.2.2.1 value)
    (imports : Store.InitializerImports store inst) (types : Store.SegmentTypeBindings store inst)
    (table : Interp.FunctionTable store inst (inst.module.module.env.func_types.val.map Store.decodeFuncType))
    (divergent : Store.instantiate_tail memory hooks floats allocator identity store platform = .div) :
    ∃ initialized index address,
      ExecutableInv view code initialized ∧ Store.SegmentObjectMetadata view store initialized ∧
      runtime.instantiate.initialize_segments memory hooks floats allocator store platform identity.index =
        .ok (.Ok (),initialized,platform) ∧
      inst.module.module.env.start = some index ∧ inst.funcs.val[index.val]? = some address ∧
      Store.instantiate_start memory hooks floats allocator identity address initialized platform = .div ∧
      Spec.InfiniteSourceWithEvents (moduleStartConfiguration view code initialized inst index) := by
  obtain ⟨initialized,status,initRun,certifiedAfter,extension,metadata,outcome⟩ :=
    instantiate_tail_executable_cases memory hooks floats allocator view laws law store platform identity inst bytes profile limits
      accepted found code certified.toCertifiedSupportedStore imports types table
  have frameMetadata : Interp.FrameStoreMetadata store initialized :=
    ⟨metadata.space.identity,metadata.space.functions,metadata.space.signatures,metadata.space.instances⟩
  have initializedInv : ExecutableInv view code initialized :=
    ⟨⟨certifiedAfter,certified.exportBounds.instances_eq metadata.space.instances⟩,
      ⟨by simpa only [metadata.space.elements,metadata.space.instances] using certified.segmentAccounting.elements,
       by simpa only [metadata.space.datas,metadata.space.instances] using certified.segmentAccounting.datas⟩,
      certified.capacities.metadata metadata.space.functions metadata.space.instances metadata.space.signatures metadata.space.identity⟩
  rcases outcome with ⟨result,returned,identityResult,source⟩ |
    ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
  · rw [returned] at divergent
    simp at divergent
  · subst status
    have afterFound : initialized.instances.val[identity.index.val]? = some inst := by
      rw [metadata.space.instances]; exact found
    rw [tailEq] at divergent
    refine ⟨initialized,index,address,initializedInv,metadata,initRun,start,mapped,divergent,?_⟩
    exact instantiate_start_executable_world_resolved_infinite memory hooks floats allocator correct law interrupts
      view laws code initialized platform initializedInv sound preserve externs issued
      identity inst afterFound index address mapped function signature owner hf hs params results divergent

end Exec.Theorems
