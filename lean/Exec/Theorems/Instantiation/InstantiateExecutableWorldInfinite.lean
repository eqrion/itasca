import Exec.Theorems.Instantiation.InstantiateExecutableEventfulSource
import Exec.Theorems.Instantiation.TailExecutableWorldInfinite
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Actual divergent host-capable instantiation has a coherent infinite labeled
source execution from its generated instantiation configuration. -/
theorem instantiate_compiled_executable_world_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : ExecutableInv view oldCode before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (raw : ModuleBinary.Module)
    (encoded : ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile)
    (sound : HostWorldSound hooks view (ExecutableInv view))
    (preserve : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → Interp.FrameStorePrefix store answer.2.2.1)
    (externs : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer → store.externs.length ≤ answer.2.2.1.externs.length)
    (issued : ∀ code store, ExecutableInv view code store →
      ∀ host p args results answer, hooks.call_host p store host args results = .ok answer →
      ∀ value ∈ answer.2.2.2.val, IssuedValue answer.2.2.1 value)
    (divergent : runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform = .div) :
    Module_ok (ModuleElaboration.moduleOf raw) ∧ ∃initial,
      fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw)
        (imports.val.map decodeExternal) initial ∧ Spec.InfiniteSourceWithEvents initial := by
  obtain ⟨actualRaw,actualEncoded,elaborated,matched,typed,origin⟩ :=
    instantiate_compiled_executable_eventful_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old.toCertifiedApiStore old.segmentAccounting handles bytes profile limits accepted
  have same := Profile.module_unique encoded actualEncoded
  subst actualRaw
  refine ⟨typed,?_⟩
  rcases origin with rejected | ⟨ready,inst,found,source,readyCertified,readyCapacities,readyAccounting,
      initializers,types,table,allocated,continued⟩
  · obtain ⟨error,staged,returned,retained⟩ := rejected
    obtain ⟨out,run,_⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run] at divergent
    simp at divergent
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    let code := installCode oldCode before.instances.length (Code.sourceFunctions raw)
    have readyInv : ExecutableInv view code ready := ⟨readyCertified,readyAccounting,readyCapacities old.capacities⟩
    have initialWf : wf_config (sourceInstantiationConfiguration view code ready inst raw) := by
      have wf : ∀ s m xs c, fun_instantiate s m xs c → wf_config c := by
        intro s m xs c h
        cases h
        assumption
      exact wf _ _ _ _ allocated
    have committed : ∀out, instantiate_tail memory hooks floats allocator ⟨before.id,before.instances.len⟩ ready platform=.ok out → out.2.2.2=true := by
      intro out actual
      obtain ⟨initialized,status,initRun,certifiedAfter,extension,metadata,cases⟩ :=
        instantiate_tail_executable_cases memory hooks floats allocator view laws law ready platform
          ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found code readyInv.toCertifiedSupportedStore initializers types table
      rcases cases with ⟨result,returned,rest⟩ | ⟨index,address,function,signature,statusEq,start,mapped,owner,hf,hs,params,results,tailEq⟩
      · rw [returned] at actual
        simp only [Result.ok.injEq] at actual
        cases actual
        rfl
      · rw [tailEq] at actual
        exact instantiate_start_returned_committed memory hooks floats allocator _ _ _ _ actual
    have tailDivergent : instantiate_tail memory hooks floats allocator ⟨before.id,before.instances.len⟩ ready platform = .div := by
      unfold runtime.store.instantiate.Store.instantiate_with at divergent
      rw [←continued] at divergent
      generalize actual : instantiate_tail memory hooks floats allocator ⟨before.id,before.instances.len⟩ ready platform=outcome at divergent
      induction outcome using Result.cases with
      | div => rfl
      | vis e k => simp at divergent
      | ret out =>
        obtain ⟨result,after,host,commit⟩ := out
        have eqCommit := committed _ actual
        dsimp only at eqCommit
        subst commit
        cases result <;> simp [runtime.store.instantiation_failed] at divergent
    obtain ⟨initialized,index,address,certified,metadata,initRun,start,mapped,tail,longRuns⟩ :=
      instantiate_tail_executable_world_infinite memory hooks floats allocator view laws correct law interrupts ready platform
        ⟨before.id,before.instances.len⟩ inst bytes profile limits acceptedInst found code readyInv sound preserve externs issued
        initializers types table tailDivergent
    have continuationWf : Forall wf_admininstr [admininstr.CALL (.mk_uN index.val)] := by
      have indexWf : wf_uN 32 (.mk_uN index.val) := by constructor; scalar_tac
      simpa [Forall] using wf_admininstr.admininstr_case_10 (.mk_uN index.val) indexWf
    have segmentRun := initialize_segments_raw_source memory hooks floats allocator view laws law ready platform
      before.instances.len inst bytes profile limits acceptedInst found code readyCertified.shape
      readyCertified.storeSyntax readyCertified.segmentBounds initializers
      (readyCertified.shape.initializer_bindings (List.mem_of_getElem? found)) types
      (moduleStartFrame ready inst) (moduleStartFrame_wf code ready before.instances.len inst readyCertified.storeSyntax found)
      rfl raw matchedInst [admininstr.CALL (.mk_uN index.val)] continuationWf
    rw [initRun, WP.spec_ok] at segmentRun
    rcases segmentRun with ⟨reason, impossible, _⟩ | ⟨_, reduced⟩
    · cases impossible
    · have frameEq : moduleStartFrame ready inst = moduleStartFrame initialized inst := by
        simp only [moduleStartFrame, decodeInstance, metadata.space.signatures]
      have rawStart : raw.start = some index := (congrArg ModuleBinary.Module.start matchedInst.1).trans start
      have sourceEq : (⟨⟨decodeStore view code ready, moduleStartFrame ready inst⟩,
          segmentRawSource raw ++ [admininstr.CALL (.mk_uN index.val)]⟩ : config) =
          sourceInstantiationConfiguration view code ready inst raw := by
        simp only [sourceInstantiationConfiguration, segmentRawSource, rawStart, Option.map_some,
          Option.toList_some, moduleStartFrame, List.append_assoc]
      rw [sourceEq, frameEq] at reduced
      have initializationSteps : StepsH (sourceInstantiationConfiguration view code ready inst raw) []
          (moduleStartConfiguration view code initialized inst index) := reduced
      exact ⟨_,allocated,longRuns.prepend initializationSteps⟩
end Exec.Theorems
