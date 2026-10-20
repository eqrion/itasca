import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Interp.StructuredMachine.SimdChosenExecution
import Exec.Interp.StructuredMachine.SimdProjection
namespace Exec.Theorems
open Aeneas Aeneas.Std Exec.Interp
theorem step_simd_supported_chosen_execution {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop} {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (interpretation : Store.CodeInterpretation)
    (memoryLaws : Platform.MemoryLaws memory view) (floatLaws : Platform.FloatOpsCorrect floats)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (raw : runtime.interp.Frame) (index : Usize) (inst : runtime.store.Instance)
    (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.SimdProjection (emission compiled) compiled.simd.val compiled.v128_pool.val] (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype) (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (source : instr) (after : List instr) (expected : List valtype)
    (last : index.val+1=exec.frames.length) (hf : exec.frames.val[index.val]?=some raw)
    (hi : store.instances.val[raw.instance.val]?=some inst)
    (hc : inst.module.functions.val[raw.function.val]?=some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view interpretation store) raw
      {f with code:=source::after} compiled C targets next output)
    (simd : Abs.SimdInstr source)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view interpretation store exec
      ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax interpretation store)
    (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view interpretation exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view interpretation store,ambient,{f with code:=source::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (StructuredMachine.Simd.step_execution_chosen admissible vector occurrence memory hooks floats allocator view interpretation memoryLaws floatLaws
    exec store platform raw index inst compiled C targets next output ambient f rest source after expected last hf hi hc program slots point simd
    (fun _ _ _ head => StructuredMachine.SimdProjection.project simd head) machine)
  intro out effect
  obtain ⟨platformEq,rawMutation,metadata,extension,normal | failed⟩ := effect
  · have mutation : CumulativeStoreMutation view interpretation store out.2.2.1 := by
      rcases rawMutation with same | ⟨address,object,issued,changed⟩
      · rw [same]; exact .refl_of_shape shaped sourceSyntax bounds
      · exact memory_mutation_cumulative_of_shape view interpretation store _ shaped sourceSyntax bounds address object issued changed
    obtain ⟨success,pc,g,fresh,simulation,owned,bounded⟩ := normal
    exact ChosenSupportedStepOutcome.success mutation success
      (StructuredMachine.ChosenAdvance.of_frame fresh simulation owned rfl bounded)
  · have mutation : CumulativeStoreMutation view interpretation store out.2.2.1 := by
      rcases rawMutation with same | ⟨address,object,issued,changed⟩
      · rw [same]; exact .refl_of_shape shaped sourceSyntax bounds
      · exact memory_mutation_cumulative_of_shape view interpretation store _ shaped sourceSyntax bounds address object issued changed
    obtain ⟨error,decoded,trace⟩ := failed
    apply ChosenSupportedStepOutcome.failure mutation error decoded
    rw [decoded] at trace
    exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,Or.inl (by simp [FloatCoreTrap])⟩,trace⟩
end Exec.Theorems
