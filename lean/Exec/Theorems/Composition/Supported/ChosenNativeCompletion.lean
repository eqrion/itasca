import Exec.Theorems.Composition.Supported.ChosenNativeOutcomes
import Exec.Theorems.Composition.Supported.ChosenLoopCompletion
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Spec Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
/-- Termination of one fixed-policy source run gives an ordinary native loop
result for the full supported language. Primitive allocation, memory, float,
interrupt and growth laws are independent of that source run. -/
theorem chosen_supported_native_loop_terminates {choices : SourceChoices} (admissible : choices.Admissible)
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
    (compatible : GrowthChoicesCompatible memory allocator view choices) (expected : List valtype)
    (initial : ChosenSupportedMachine emission allowed M P view code expected)
    {events : List HostEvent} {target : config}
    (run : ChoiceSteps choices initial.occurrence (Abs.decode initial.source) events target)
    (terminal : SourceTerminal target) :
    runtime.interp.invoke_with_loop2 memory hooks floats allocator initial.exec initial.store initial.platform (.Ok ())
      ⦃ result => ∃ state, ChosenSupportedLoopInvariant (choices:=choices) memory hooks floats allocator initial state ∧
        ¬ActiveExecution state ∧ finishExecution state=result ⦄ := by
  exact chosen_supported_loop_terminates admissible memory hooks floats allocator
    (chosen_supported_step_outcomes admissible numericChoice vector language memory hooks floats allocator correct allocation
      interrupts view laws code compatible expected) initial run terminal
end Exec.Theorems
