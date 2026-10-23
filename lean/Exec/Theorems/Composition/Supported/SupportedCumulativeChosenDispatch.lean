import Exec.Theorems.Api.GrowthChoiceMatching
import Exec.Theorems.Composition.Supported.SupportedHeadChosenBase
import Exec.Theorems.Composition.Supported.SupportedScalarChosenExecution
import Exec.Theorems.Composition.Supported.SupportedStatefulChosenExecution
import Exec.Theorems.Composition.Supported.SupportedIndirectChosenExecution
import Exec.Theorems.Composition.Core.CoreHostFree
import Exec.Interp.Machines.Cumulative.CumulativeHeadCoverage
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Interp
theorem step_head_supported_chosen_cumulative {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (numericChoice : choices.numeric=Spec.firstNumericChoice) (vector : choices.vector=Spec.firstVectorChoice)
    (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    [∀ compiled, StructuredMachine.FloatHeads (emission compiled)]
    [∀ compiled, StructuredMachine.OrdinaryHeads (emission compiled)]
    [∀ compiled, StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    [∀ compiled, StructuredMachine.IndirectProjection (emission compiled) compiled.indirect.val]
    (language : Abs.Supported.Language allowed) {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (correct : Platform.FloatOpsCorrect floats)
    (allocation : Platform.AllocCorrect allocator) (interrupts : ∀ p, hooks.interrupt p ⦃ _ => True ⦄)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (compatible : GrowthChoicesCompatible memory allocator view choices)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index : Usize) (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst)
    (compiled : runtime.bytecode.CompiledFunction) (C : context)
    (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (op : instr) (after : List instr)
    (head : CumulativeDispatchHead op)
    (last : index.val+1 = exec.frames.length) (hf : exec.frames.val[index.val]? = some raw)
    (hi : store.instances.val[raw.instance.val]? = some inst)
    (hc : inst.module.functions.val[raw.function.val]? = some compiled)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (slots : FrameSlots exec raw f)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (small : ∀ object ∈ store.globals.val, object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (point : StructuredMachine.FramePoint emission (Store.decodeStore view code store) raw {f with code := op::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩ expected raw.pc.val false)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store)
    (compiledFunctions : StructuredMachine.CompiledFunctions emission code store) (functionTyping : CoreFunctionsTyped view code store) (free : CoreHostFree store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store)
      ⟨Store.decodeStore view code store,ambient,{f with code := op::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op::after}::rest,[]⟩ out ⦄ := by
  cases head with
  | core head =>
    rcases step_head_supported_chosen_base admissible vector occurrence language memory hooks floats allocator allocation interrupts view laws code exec store platform index raw inst compiled C targets next output
      ambient f rest op after head last hf hi hc program slots moduleEq small point expected machine shaped sourceSyntax bounds compiledFunctions functionTyping owned with host | result
    · exact (free.no_boundary exec host).elim
    · exact result
  | scalar operation =>
    apply WP.spec_mono (step_scalar_supported_chosen_execution admissible numericChoice occurrence language memory hooks floats allocator correct exec store platform index raw inst compiled C targets next output
      view code ambient f rest operation after last hf hi hc slots point expected machine program shaped sourceSyntax bounds)
    intro out result
    exact result.2.2
  | stateful operation =>
    exact stateful_chosen_execution_supported admissible vector occurrence language memory hooks floats allocator allocation view laws code compatible exec store platform index raw inst compiled C targets next output
      ambient f rest after operation last hf hi hc moduleEq slots point expected machine program shaped sourceSyntax bounds owned
  | indirect table type =>
    rcases step_indirect_supported_chosen_execution admissible vector occurrence language memory hooks floats allocator allocation interrupts view code exec store platform index raw inst compiled C targets next output
      ambient f rest table type after last hf hi hc moduleEq program slots point expected machine shaped compiledFunctions functionTyping with host | operation
    · obtain ⟨f,rest,table,type,position,after,front,address,function,host,_,_,_,_,found,defined⟩ := host
      exact (free function (List.mem_of_getElem? found) host defined).elim
    · apply WP.spec_mono operation
      intro out result
      cases status : out.1 with
      | Ok unit =>
        cases unit
        exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds result.1 status (result.2.1 status)
      | Err error =>
        apply ChosenSupportedStepOutcome.failure (by rw [result.1];exact .refl_of_shape shaped sourceSyntax bounds) status (by simp only [result.1])
        rcases result.2.2 error status with ⟨⟨trap,errorEq,kind⟩,steps⟩ | cause
        · exact Or.inl ⟨⟨trap,errorEq,Or.inr kind⟩,steps⟩
        · exact Or.inr (Or.inr ⟨index,raw,inst,compiled,last,hf,hi,hc,Or.inr ⟨code,cause⟩⟩)
end Exec.Theorems
