import Exec.Theorems.Composition.Supported.SupportedExecutionOutcome
import Exec.Theorems.Composition.StoreMutationFacts
import Exec.Theorems.Composition.Stateful.StatefulReferenceShape
import Exec.Theorems.Api.StatefulTableGrowStep
import Exec.Interp.StructuredMachine.JumpExecution
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Spec Exec.Interp
theorem stateful_table_grow_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (allocation : Platform.AllocCorrect allocator) (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (tableIndex : Nat)
    (last : index.val+1=exec.frames.length) (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (decodeStore view code store) raw {f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS)
    (shaped : Shape view store) (sourceSyntax : StoreSyntax code store) (bounds : SegmentBounds store)
    (owned : Abs.Ownership.StatefulOwned (Store.ownershipBounds store) ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩) :
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      SupportedStepOutcome allocator hooks view code exec store platform expected compiled.code.length raw.pc.val false
        ⟨decodeStore view code store,ambient,{f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after}::rest,[]⟩ out ⦄ := by
  rcases stateful_table_grow_point_step memory hooks floats allocator allocation view code exec store platform index raw inst compiled C targets next output
    ambient f rest after tableIndex last frameFound found codeFound program.fetchBound (fun object member => (shaped.tables object member).1) moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
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
    exact StructuredMachine.ordinary_cumulative_step view code ambient {f with code:=(Abs.Stateful.Instruction.tableGrow tableIndex).source::after}
      {f with code:=after,vals:=front++[Abs.integerVal .I32 result.val]} rest expected raw.pc.val false
      machine metadata raw index pc last frameFound program (.ready retained) represented ⟨rfl,rfl,rfl,rfl⟩
      written.2 (by rw [written.1]; exact SlotPrefix.set _ _ _ _ above) transition

end Exec.Theorems
