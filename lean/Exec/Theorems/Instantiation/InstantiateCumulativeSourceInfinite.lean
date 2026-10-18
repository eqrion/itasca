import Exec.Theorems.Instantiation.InstantiateCumulativeSource
import Exec.Theorems.Instantiation.TailCumulative
import Exec.Theorems.Instantiation.TailCumulativeInfinite
namespace Exec.Theorems
open Aeneas Aeneas.Std Itasca Store SpecExt

/-- Actual public divergence yields an infinite source reduction beginning
at the generated instantiation configuration, including its segment prefix. -/
theorem instantiate_compiled_cumulative_source_infinite {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (correct : Platform.FloatOpsCorrect floats)
    (law : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (before : runtime.store.Store M) (module : runtime.compiler.ExecutableModule)
    (imports : Slice runtime.Extern) (platform : P)
    (oldCode : CodeInterpretation) (old : CertifiedCumulativeStore view oldCode before)
    (hostFree : CoreHostFree before)
    (accounted : SegmentAccounting before)
    (handles : ∀ external ∈ imports.val, ExternalIssued before external)
    (bytes : Slice U8) (profile : ValidationProfile) (limits : runtime.compiler.CompileLimits)
    (supported : Code.SourceCumulative profile bytes)
    (accepted : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok module))
    (divergent : runtime.store.instantiate.Store.instantiate_with memory hooks floats allocator before module imports platform = .div) :
    ∃ raw initial,
      ModuleBinary.ModuleEncodingWith (Profile.CodeEncoding profile) raw bytes.val profile ∧
      Module_ok (ModuleElaboration.moduleOf raw) ∧ Code.ModuleCumulative raw ∧
      fun_instantiate (decodeStore view oldCode before) (ModuleElaboration.moduleOf raw)
        (imports.val.map decodeExternal) initial ∧
      Spec.InfiniteSource initial := by
  obtain ⟨raw, encoded, elaborated, matched, typed, sliced, origin⟩ :=
    instantiate_compiled_cumulative_source_origin memory hooks floats allocator view laws law before module imports platform
      oldCode old hostFree accounted handles bytes profile limits supported accepted
  rcases origin with rejected | ⟨ready, inst, found, source, readyCertified, readyHostFree, readyAccounting,
      initializers, types, table, allocated, continued⟩
  · obtain ⟨error, staged, returned, retained⟩ := rejected
    obtain ⟨out, run, _⟩ := WP.spec_imp_exists
      (instantiate_rollback memory hooks floats allocator before staged module imports platform platform error retained returned)
    rw [run] at divergent
    simp at divergent
  · have acceptedInst : runtime.compiler.compile_with allocator bytes profile limits = .ok (.Ok inst.module) := by
      simpa only [source] using accepted
    have matchedInst : ModuleElaboration.Matches inst.module.module.env inst.module.module.tail raw := by
      simpa only [source] using matched
    let code := installCode oldCode before.instances.length (Code.sourceFunctions raw)
    have normal := instantiate_tail_cumulative memory hooks floats allocator view laws correct law interrupts ready platform
      ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found
      code readyCertified readyHostFree initializers types table
    have tailDivergent : instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform = .div := by
      generalize actual : instantiate_tail memory hooks floats allocator ⟨before.id, before.instances.len⟩ ready platform = outcome at normal
      cases normal with
      | div => rfl
      | @ret _ out post =>
        obtain ⟨result, after, host, committed⟩ := out
        have commit := post.1
        dsimp only at commit
        subst committed
        unfold runtime.store.instantiate.Store.instantiate_with at divergent
        rw [← continued, actual] at divergent
        cases result <;> simp [runtime.store.instantiation_failed] at divergent
    obtain ⟨initialized, index, address, certified, metadata, initRun, start, mapped, tail, longRuns⟩ :=
      instantiate_tail_cumulative_infinite memory hooks floats allocator view laws correct law interrupts ready platform
        ⟨before.id, before.instances.len⟩ inst bytes profile limits acceptedInst found code readyCertified readyHostFree
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
      exact ⟨raw, _, encoded, typed, sliced, allocated, longRuns.prepend initializationSteps⟩
end Exec.Theorems
