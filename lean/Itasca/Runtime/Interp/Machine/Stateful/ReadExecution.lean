import Itasca.Runtime.Interp.State.StatefulReadStep
import Itasca.Runtime.Interp.Machine.Coverage.SupportedControlSemantics
import Itasca.Runtime.Interp.Machine.Control.JumpExecution
import Itasca.Runtime.Interp.Relations.Capacity

/-!
Stateful read execution under the supported-source relation.

Main declarations: `read_execution_supported_forward` and `read_execution_supported`. A direct consumer is `Integration.Execution.Dispatch.StoreRead`.
-/

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec

theorem read_execution_supported_forward
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧ out.2.2.2=platform ∧
      ((out.1=.Ok () ∧ ∃ pc : U32,∃ g : Abs.AFrame, raw.pc.val < pc.val ∧
        StructuredMachine.Execution view code store out.2.1 ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        (∀ bounds,Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) ∧
        (∀ bound,Abs.CodeBound bound initial → Abs.CodeBound bound ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩)) ∨
       (out.1=.Err (.Trap .TableOutOfBounds) ∧ ∃ n,0<n ∧ StepsHN n (Abs.decode initial) []
         ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have top : exec.frames.val.getLast?=some raw := by
    rw [List.getLast?_eq_getElem?]
    have position : exec.frames.val.length-1=index.val := by change exec.frames.length-1=index.val; omega
    rw [position]
    exact frameFound
  have allocated := (machine.stack.top raw top).binding.capacity inst compiled found codeFound
  rcases read_point_step memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after op
    readOnly last frameFound found codeFound program.checked program.fetchBound allocated moduleEq slots point machine.typed with jump | actual
  · obtain ⟨target,forward,fetch,retained⟩ := jump
    apply WP.spec_mono (StructuredMachine.step_forward_jump memory hooks floats allocator view code exec store platform index raw inst compiled ambient
      {f with code:=op.source::after} rest expected C targets next output target last frameFound found codeFound forward fetch slots retained machine program)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,fresh,simulation⟩ := effect
    exact ⟨sameStore,samePlatform,Or.inl ⟨success,target,_,forward,fresh,simulation,fun _ h => h,fun _ h => h⟩⟩
  · apply WP.spec_mono actual
    intro out effect
    obtain ⟨sameStore,samePlatform,operation⟩ := effect
    refine ⟨sameStore,samePlatform,?_⟩
    rcases operation with ⟨pc,produced,position,word,success,pcNext,above,bound,written,represented,retained,transition⟩ | ⟨error,exactState,transition⟩
    · have freshTyped := transition.next_typed_supported machine.typed machine.core
      have freshCovered := transition.next_covered_supported machine.typed machine.core
      have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
        rw [written.1]
        exact .set _ _ _ _ above
      have execution := StructuredMachine.Execution.ordinary view code ambient {f with code:=op.source::after}
        {f with code:=after,vals:=produced} rest expected raw.pc.val false machine (.refl store)
        (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound program (.ready retained) represented
        ⟨rfl,rfl,rfl,rfl⟩ written.2 preserved freshTyped freshCovered
      exact Or.inl ⟨success,pc,_,by omega,execution,ConcreteSim.of_source _ _ _ _ _ (transition.next_simulation_supported machine.typed machine.core),
        fun _ h => transition.next_owned_supported machine.typed machine.core h,
        fun _ h => transition.next_bound_supported machine.typed machine.core h⟩
    · exact Or.inr ⟨error,transition.trap_simulation_supported machine.typed machine.core⟩

theorem read_execution_supported
 {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P) (index : Usize)
    (raw : runtime.interp.Frame) (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    [StructuredMachine.StatefulProjection (emission compiled) compiled.indirect.val]
    (C : context) (targets : List Code.LabelTarget) (next : Nat) (output : List valtype)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (op : Abs.Stateful.Instruction)
    (readOnly : op.readOnly=true) (last : index.val+1=exec.frames.length)
    (frameFound : exec.frames.val[index.val]?=some raw)
    (found : store.instances.val[raw.instance.val]?=some inst)
    (codeFound : inst.module.functions.val[raw.function.val]?=some compiled)
    (moduleEq : f.module=Store.decodeInstance store inst) (slots : FrameSlots exec raw f)
    (point : StructuredMachine.FramePoint (Store.decodeStore view code store) raw {f with code:=op.source::after} compiled C targets next output)
    (expected : List valtype)
    (machine : StructuredMachine.Execution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code:=op.source::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1=store ∧ out.2.2.2=platform ∧
      ((out.1=.Ok () ∧ ∃ pc : U32,∃ g : Abs.AFrame,
        StructuredMachine.Execution view code store out.2.1 ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ ∧
        (∀ bounds,Abs.Ownership.StatefulOwned bounds initial → Abs.Ownership.StatefulOwned bounds ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩) ∧
        (∀ bound,Abs.CodeBound bound initial → Abs.CodeBound bound ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩)) ∨
       (out.1=.Err (.Trap .TableOutOfBounds) ∧ ∃ n,0<n ∧ StepsHN n (Abs.decode initial) []
         ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  apply WP.spec_mono (read_execution_supported_forward memory hooks floats allocator view laws code exec store platform index raw inst compiled C targets next output ambient f rest after op readOnly last frameFound found codeFound moduleEq slots point expected machine program)
  rintro out ⟨sameStore,samePlatform,normal | failed⟩
  · obtain ⟨ok,pc,g,forward,fresh⟩ := normal
    exact ⟨sameStore,samePlatform,Or.inl ⟨ok,pc,g,fresh⟩⟩
  · exact ⟨sameStore,samePlatform,Or.inr failed⟩

end Itasca.Runtime.Interp.Stateful
