import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Integration.Execution.TableInit
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Interp.Machine.Stateful.ReadExecution
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Integration.Execution.TableSetStep

/-!
Sections, each formerly its own module: SegmentDrop, StoreRead, TableSet.
-/

/-! ## SegmentDrop -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp
theorem StatefulDropEffect.mutation_of_shape {M : Type} {view : M → Slice U8} {code : CodeInterpretation}
    {before after : runtime.store.Store M} (effect : StatefulDropEffect before after)
    (shaped : Shape view before) (sourceSyntax : StoreSyntax code before) (bounds : SegmentBounds before) : CumulativeStoreMutation view code before after := by
  cases effect with
  | data address issued => exact data_drop_cumulative_mutation_of_shape shaped sourceSyntax bounds (List.getElem?_eq_getElem issued)
  | element address issued => exact element_drop_cumulative_mutation_of_shape shaped sourceSyntax bounds (List.getElem?_eq_getElem issued)

theorem stateful_drop_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Stateful.Instruction) (isDrop : statefulIsDrop op=true)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_drop_point_step memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
    ambient f rest after op isDrop last frameFound found codeFound program.fetchBound moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=op.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨success,samePlatform,effect,metadata,pc,pcNext,exactState,represented,retained,transition⟩ := result
    have mutation := effect.mutation_of_shape shaped sourceSyntax bounds
    apply SupportedStepOutcome.success mutation success
    exact Machine.ordinary_cumulative_step view code ambient {f with code:=op.source::after} {f with code:=after} rest expected raw.pc.val false
      machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
      (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition

end Itasca.Runtime.Integration

end

/-! ## StoreRead -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std Itasca.Runtime.Interp
theorem stateful_read_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (op : SourceMachine.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Store.Shape view store) (sourceSyntax : Store.StoreSyntax code store) (bounds : Store.SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ out ⦄ := by
  apply WP.spec_mono (Stateful.read_execution_supported memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after op readOnly last frameFound found codeFound moduleEq slots point expected machine program)
  intro out result
  obtain ⟨sameStore,samePlatform,operation⟩ := result
  rcases operation with ⟨success,pc,g,fresh,simulation,owned,bound⟩ | ⟨error,trap⟩
  · exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨pc.val,false,_,fresh,simulation,owned,rfl,bound⟩
  · apply SupportedStepOutcome.failure (by rw [sameStore];exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
    exact Or.inl ⟨⟨.TableOutOfBounds,rfl,Or.inr (Or.inl rfl)⟩,trap⟩

end Itasca.Runtime.Integration

end

/-! ## TableSet -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp
theorem stateful_table_set_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (tableIndex : Nat)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_table_set_point_step memory hooks floats allocator view code exec store platform index raw inst compiled C targets next output
    ambient f rest after tableIndex last frameFound found codeFound program.fetchBound moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨samePlatform,metadata,operation⟩ := result
    rcases operation with ⟨pc,front,success,pcNext,exactState,rawEffect,represented,retained,transition⟩ | ⟨error,sameStore,exactState,transition⟩
    · obtain ⟨address,object,source,issued,effect,member⟩ := rawEffect
      have reference := Store.owned_reference_shape store object.ty source ((owned.values.2 _ (List.mem_cons_self ..)).2 _ member)
      have mutation := table_mutation_cumulative_of_shape view code store out.2.2.1 shaped sourceSyntax bounds address object source issued effect reference
      apply SupportedStepOutcome.success mutation success
      exact Machine.ordinary_cumulative_step view code ambient {f with code:=(SourceMachine.Stateful.Instruction.tableSet tableIndex).source::after} {f with code:=after,vals:=front} rest expected raw.pc.val false
        machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
        (by rw [exactState]) (by rw [exactState]; exact .refl _ _) transition
    · apply SupportedStepOutcome.failure (by rw [sameStore]; exact .refl_of_shape shaped sourceSyntax bounds) error (by rw [sameStore])
      exact Or.inl ⟨⟨.TableOutOfBounds,rfl,by simp [CumulativeTrap,FloatCoreTrap]⟩,transition.trap_simulation_supported machine.typed machine.core⟩




end Itasca.Runtime.Integration

end
