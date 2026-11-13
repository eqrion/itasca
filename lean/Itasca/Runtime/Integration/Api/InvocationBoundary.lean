import Itasca.Runtime.Integration.Execution.Dispatch.Outcomes
import Itasca.Runtime.Integration.Execution.Mutation.Operations
import Itasca.Runtime.Integration.Api.InitialHostInvocationCauses
import Itasca.Runtime.Interp.Machine.Control.BranchSource
import Itasca.Runtime.Integration.Execution.Ownership.ReferenceShape
import Itasca.Runtime.Interp.Invocation.Recording
import Itasca.Runtime.Integration.Execution.Ownership.Entry
import Itasca.Runtime.Store.Invariant.HostSignature
import Itasca.Runtime.Spec.ModuleMembership
import Itasca.Generated.Types

/-!
Sections, each formerly its own module: SupportedMemoryGrowExecution, SupportedTableGrowExecution, ReadbackIssued, InvocationBoundary.
-/

/-! ## SupportedMemoryGrowExecution -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp
theorem stateful_memory_grow_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_memory_grow_point_step memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output
    ambient f rest after last frameFound found codeFound program.fetchBound shaped.memories moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨success,samePlatform,metadata,pc,front,position,result,pcNext,above,inSlots,written,rawEffect,represented,retained,transition⟩ := result
    obtain ⟨address,delta,issued,effect⟩ := rawEffect
    have mutation := memory_growth_cumulative_mutation_of_shape shaped sourceSyntax bounds issued effect (transition.next_extends_supported machine.typed machine.core)
    apply SupportedStepOutcome.success mutation success
    exact Machine.ordinary_cumulative_step view code ambient {f with code:=SourceMachine.Stateful.Instruction.memoryGrow.source::after}
      {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest expected raw.pc.val false
      machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
      written.2 (by rw [written.1]; exact SlotPrefix.set _ _ _ _ above) transition

end Itasca.Runtime.Integration

end

/-! ## SupportedTableGrowExecution -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store Itasca.Runtime.Spec Itasca.Runtime.Interp
theorem stateful_table_grow_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [Machine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Compiler.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (tableIndex : Nat)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : Machine.FramePoint (decodeStore view code store) raw {f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : Machine.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Compiler.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store)
    (owned : SourceMachine.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_table_grow_point_step memory hooks floats allocator allocation view code exec store platform index raw inst compiled C targets next output
    ambient f rest after tableIndex last frameFound found codeFound program.fetchBound (fun object member => (shaped.tables object member).1) moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (Machine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out result
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := result
    exact SupportedStepOutcome.unchanged_success shaped sourceSyntax bounds sameStore success ⟨target.val,false,_,fresh,simulation,fun _ h => h,rfl,fun _ h => h⟩
  · apply WP.spec_mono actual
    intro out result
    obtain ⟨success,samePlatform,metadata,pc,front,position,result,pcNext,above,inSlots,written,rawEffect,represented,retained,transition⟩ := result
    obtain ⟨address,object,delta,reference,issued,effect,member⟩ := rawEffect
    have inBounds := (List.getElem?_eq_some_iff.mp issued).1
    have objectEq := (List.getElem?_eq_some_iff.mp issued).2
    have referenceShape := Store.owned_reference_shape store object.ty reference ((owned.values.2 _ (List.mem_cons_self ..)).2 _ member)
    have mutation := table_growth_cumulative_mutation_of_shape shaped sourceSyntax bounds inBounds (by simpa only [objectEq] using referenceShape) effect (transition.next_extends_supported machine.typed machine.core)
    apply SupportedStepOutcome.success mutation success
    exact Machine.ordinary_cumulative_step view code ambient {f with code:=(SourceMachine.Stateful.Instruction.tableGrow tableIndex).source::after}
      {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 result.val]} rest expected raw.pc.val false
      machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
      written.2 (by rw [written.1]; exact SlotPrefix.set _ _ _ _ above) transition

end Itasca.Runtime.Integration

end

/-! ## ReadbackIssued -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Interp

theorem owned_source_value_in_store {M : Type} (store : runtime.store.Store M) (value : runtime.Value)
    (owner : OwnedBy store.id value)
    (sourceOwned : SourceMachine.Ownership.ValueOwned (Store.ownershipBounds store) (sourceValue value)) :
    Store.ValueInStore store value := by
  have issued : Store.IssuedValue store value := by
    cases value <;> try trivial
    all_goals rename_i reference
    all_goals cases reference with
    | none => trivial
    | some reference => exact fun _ => sourceOwned
  exact issued.in_store owner

end Itasca.Runtime.Integration

end

/-! ## InvocationBoundary -/

section

namespace Itasca.Runtime.Integration
open Aeneas Aeneas.Std SpecExt
/-- Call-stack exhaustion is bounded by decoded frame nesting; termination
retains a concrete interrupt decision. -/
def InvocationBoundaryCause {M P : Type} (hooks : runtime.platform.Platform P M)
    (initial : config) (maxFrames : Nat) : runtime.ExecError → Prop
  | .Exhausted .CallStack => maxFrames ≤ Spec.frameDepth initial ∨
      ∃ final, StepsH initial [] final ∧ maxFrames ≤ Spec.frameDepth final
  | .Terminated => ∃ before after, hooks.interrupt before = .ok (.Terminate, after)
  | _ => True

end Itasca.Runtime.Integration

end
