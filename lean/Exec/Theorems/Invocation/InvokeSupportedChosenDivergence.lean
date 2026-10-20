import Exec.Theorems.Invocation.InvokeSupportedDivergence
import Exec.Theorems.Composition.Supported.ChosenNativeOutcomes
import Exec.Theorems.Composition.Supported.ChosenMachineDivergence
import Exec.Spec.Choices.NeutralStep
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
variable {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
/-- Actual host-free public invocation divergence preserves the preselected
source policy, including the call-address entry occurrence. -/
theorem invoke_defined_supported_infinite_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat)
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
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator)
    (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (certified : CertifiedSupportedStore emission allowed view code store) (hostFree : CoreHostFree store)
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
    Spec.InfiniteChosenSource choices occurrence
      ⟨⟨Store.decodeStore view code store,ambient⟩,
        vals (args.val.map Interp.sourceValue) ++ [.CALL_ADDR address.index.val]⟩ := by
  obtain ⟨machine,entry,divergent⟩ := invoke_supported_divergent_machine language memory hooks floats allocator correct allocation
    interrupts view laws code exec store platform certified hostFree ambient ambientWf address function signature instanceIndex functionIndex
    args results owner owned hf hs hw divergent
  have chosenEntry := Spec.stepH_neutral_chosen admissible vector occurrence entry (by
    simp only [Spec.trapCode,Spec.neutralActive_vals,Spec.neutralActive])
  let selected : ChosenSupportedMachine emission allowed M P view code (signature.results.val.map Interp.sourceType) :=
    ⟨machine,occurrence+1⟩
  exact Spec.InfiniteChosenSource.prepend_step chosenEntry
    (chosen_supported_loop_infinite memory hooks floats allocator
      (chosen_supported_step_outcomes admissible numericChoice vector language memory hooks floats allocator correct allocation
        interrupts view laws code compatible _) selected divergent)
end Exec.Theorems
