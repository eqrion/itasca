import Exec.Theorems.Composition.Supported.ChosenMachine
import Exec.Theorems.Composition.Supported.SupportedChosenStepCertified
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}

/-- Every actual supported native dispatch constructs the chosen edge. Float
and growth compatibility are primitive laws, independent of execution traces. -/
theorem chosen_supported_step_outcomes {choices : SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=firstNumericChoice) (vector : choices.vector=firstVectorChoice)
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val]
    [∀ compiled, StructuredMachine.TypedSelectHeads (emission compiled)]
    [∀ compiled, StructuredMachine.SupportedHeads (emission compiled)]
    [∀ compiled, StructuredMachine.ErasedHeads (emission compiled)]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats) (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p,hooks.interrupt p ⦃ _=>True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices) (expected : List valtype) :
    ChosenSupportedStepOutcomes (emission:=emission) (allowed:=allowed) choices memory hooks floats allocator view code expected := by
  intro before active
  obtain ⟨⟨status,nextExec,nextStore,nextPlatform⟩,actual,fresh,extension,bounds,hostFree,mutation,outcome⟩ :=
    WP.spec_imp_exists (step_supported_chosen_host_free admissible numericChoice vector before.occurrence language
      memory hooks floats allocator correct allocation interrupts view laws code compatible before.exec before.store before.platform
      before.source expected before.pc before.pending before.certified before.hostFree before.owned before.invariant active)
  rw [actual,WP.spec_ok]
  refine ⟨mutation,?_⟩
  cases status with
  | Err error => exact outcome
  | Ok unit =>
    cases unit
    obtain ⟨pc,pending,source,retained,simulation,ownership,ambient,bounded⟩ := outcome
    have owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds nextStore) source := by
      rw [bounds]
      exact ownership _ before.owned
    let core : SupportedMachine emission allowed M P view code expected :=
      ⟨nextStore,nextExec,nextPlatform,source,pc,pending,retained,fresh,owned,hostFree⟩
    have recorded : SupportedTransition memory hooks floats allocator before.toSupportedMachine [] core :=
      ⟨rfl,actual,simulation.erases admissible,extension,mutation.metadata,ambient,bounded,mutation.segmentCounts,mutation.limits⟩
    rcases simulation with ⟨same,decrease⟩ | ⟨count,positive,sourceSteps⟩
    · let after : ChosenSupportedMachine emission allowed M P view code expected := ⟨core,before.occurrence⟩
      exact ⟨after,rfl,recorded,Or.inl ⟨same,rfl,rfl,decrease⟩⟩
    · let after : ChosenSupportedMachine emission allowed M P view code expected := ⟨core,before.occurrence+count⟩
      exact ⟨after,rfl,recorded,Or.inr ⟨count,positive,rfl,sourceSteps⟩⟩
end Exec.Theorems
