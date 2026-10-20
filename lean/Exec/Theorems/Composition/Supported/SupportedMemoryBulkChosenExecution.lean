import Exec.Theorems.Composition.Supported.ChosenSupportedOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Theorems.Composition.Stateful.StatefulMemoryFillChosenStep
import Exec.Theorems.Composition.Stateful.StatefulMemoryCopyChosenStep
import Exec.Theorems.Composition.Stateful.StatefulMemoryInitChosenStep
import Exec.Interp.StructuredMachine.JumpExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp

theorem stateful_memory_fill_execution_supported_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    (language : Abs.Supported.Language allowed) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (decodeStore view code store) raw {f with code:=Abs.Stateful.Instruction.memoryFill.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨decodeStore view code store,ambient,{f with code:=Abs.Stateful.Instruction.memoryFill.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=Abs.Stateful.Instruction.memoryFill.source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_memory_fill_point_step_chosen occurrence memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after last frameFound found codeFound program.fetchBound shaped.memories moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=Abs.Stateful.Instruction.memoryFill.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward retained.code.current.entry_bound⟩,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨samePlatform,metadata,operation⟩ := result
    rcases operation with ⟨pc,front,success,pcNext,exactState,rawEffect,represented,retained,transition⟩ | ⟨error,sameStore,exactState,transition⟩
    · obtain ⟨address,object,destination,source,count,issued,effect⟩ := rawEffect
      have mutation := memory_fill_cumulative_mutation_of_shape shaped sourceSyntax bounds issued effect
      apply ChosenSupportedStepOutcome.success mutation success
      exact StructuredMachine.ordinary_chosen_cumulative_step admissible vector occurrence language view code ambient {f with code:=Abs.Stateful.Instruction.memoryFill.source::after} {f with code:=after,vals:=front} rest expected raw.pc.val false
        machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
        (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition
    · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,by simp [CumulativeTrap,FloatCoreTrap]⟩,transition.trap_simulation admissible vector language machine.typed machine.core⟩


theorem stateful_memory_copy_execution_supported_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    (language : Abs.Supported.Language allowed) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (decodeStore view code store) raw {f with code:=Abs.Stateful.Instruction.memoryCopy.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨decodeStore view code store,ambient,{f with code:=Abs.Stateful.Instruction.memoryCopy.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=Abs.Stateful.Instruction.memoryCopy.source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_memory_copy_point_step_chosen occurrence memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after last frameFound found codeFound program.fetchBound moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=Abs.Stateful.Instruction.memoryCopy.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward retained.code.current.entry_bound⟩,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨samePlatform,metadata,operation⟩ := result
    rcases operation with ⟨pc,front,success,pcNext,exactState,rawEffect,represented,retained,transition⟩ | ⟨error,sameStore,exactState,transition⟩
    · obtain ⟨address,object,destination,source,count,issued,effect⟩ := rawEffect
      have mutation := memory_copy_cumulative_mutation_of_shape shaped sourceSyntax bounds issued effect
      apply ChosenSupportedStepOutcome.success mutation success
      exact StructuredMachine.ordinary_chosen_cumulative_step admissible vector occurrence language view code ambient {f with code:=Abs.Stateful.Instruction.memoryCopy.source::after} {f with code:=after,vals:=front} rest expected raw.pc.val false
        machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
        (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition
    · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,by simp [CumulativeTrap,FloatCoreTrap]⟩,transition.trap_simulation admissible vector language machine.typed machine.core⟩


theorem stateful_memory_init_execution_supported_chosen {choices : Spec.SourceChoices} (admissible : choices.Admissible)
    (vector : choices.vector=Spec.firstVectorChoice) (occurrence : Nat) {emission : StructuredMachine.FunctionEmission} {allowed : instr → Prop}
    (language : Abs.Supported.Language allowed) {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (dataIndex : Nat)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint emission (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution emission (Abs.SupportedState allowed) view code store exec ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      ChosenSupportedStepOutcome choices occurrence emission allowed allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_memory_init_point_step_chosen occurrence memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after dataIndex last frameFound found codeFound program.fetchBound shaped.memories bounds moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact ChosenSupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,Or.inl ⟨rfl,dispatchMeasure_forward _ _ _ _ forward retained.code.current.entry_bound⟩,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨samePlatform,metadata,operation⟩ := result
    rcases operation with ⟨pc,front,success,pcNext,exactState,rawEffect,represented,retained,transition⟩ | ⟨error,sameStore,exactState,transition⟩
    · obtain ⟨address,object,segment,destination,source,count,issued,effect⟩ := rawEffect
      have mutation := memory_init_cumulative_mutation_of_shape shaped sourceSyntax bounds issued effect
      apply ChosenSupportedStepOutcome.success mutation success
      exact StructuredMachine.ordinary_chosen_cumulative_step admissible vector occurrence language view code ambient {f with code:=(Abs.Stateful.Instruction.memoryInit dataIndex).source::after} {f with code:=after,vals:=front} rest expected raw.pc.val false
        machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
        (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition
    · apply ChosenSupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
      exact Or.inl ⟨⟨.MemoryOutOfBounds,rfl,by simp [CumulativeTrap,FloatCoreTrap]⟩,transition.trap_simulation admissible vector language machine.typed machine.core⟩

end Exec.Theorems
