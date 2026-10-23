import Exec.Interp.Machines.Core.CoreOwnership
import Exec.Interp.Machines.Core.CoreBound
import Exec.Interp.Memory.MemoryCoreRun
import Exec.Interp.Core.OrdinaryExecution
namespace Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Exec.Spec
theorem step_memory_load_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Load) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        CoreExecution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.CoreOwned bounds initial → Abs.Ownership.CoreOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_load_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,offset,input,position,offsetEq,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_memory_load_core memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed)
  intro out effect
  obtain ⟨sameStore,samePlatform,operation⟩ := effect
  rw [sameStore]
  refine ⟨samePlatform,Or.inl rfl,.refl store,extend_store_refl _ machine.typed.typed.store,?_⟩
  rcases operation with ⟨success,pc,g,fields,represented,retained,fresh,metadata,transition,simulation,footprint⟩ | ⟨failed,trace⟩
  · have covered : Abs.CoreState ⟨Store.decodeStore view code store,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact Abs.Core.step_core _ _ machine.typed.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rcases footprint with same | ⟨position,word,above,bound,changed⟩
      · rw [same]; exact .refl _ _
      · rw [changed]; exact .set _ _ _ _ above
    exact Or.inl ⟨success,pc,g,CoreExecution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      (.refl store) (extend_store_refl _ machine.typed.typed.store) raw index pc last frameFound
      program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ fields preserved fresh covered,simulation,core_owned_transition machine.typed machine.core transition,core_bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,rfl,trace⟩

theorem step_memory_store_execution_owned {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.ModuleInst) (compiled : runtime.bytecode.CompiledFunction)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (op : Abs.Memory.Store) (argument : memarg) (C : context) (targets : List Code.LabelTarget)
    (next : Nat) (output : List valtype)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (point : CoreFramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (expected : List valtype)
    (machine : CoreExecution view code store exec
      ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩ expected raw.pc.val false)
    (program : FrameProgram store raw compiled (f.locals.map Code.valueType) f.resultTypes C.FUNCS) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument::after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        CoreExecution view code out.2.2.1 out.2.1
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} expected pc.val false ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧
        (∀ bounds, Abs.Ownership.CoreOwned bounds initial → Abs.Ownership.CoreOwned bounds {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        (∀ bound, Abs.CodeBound bound initial → Abs.CodeBound bound {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest})) ∨
       (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) []
          ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have pcBound : raw.pc.val < U32.max := by
    rcases corePoint_store_head op argument after point.code with ⟨target,forward,fetched,tail⟩ | ⟨types,address,value,offset,input,position,valuePosition,offsetEq,fetched,tail⟩
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
    · have bound := (List.getElem?_eq_some_iff.mp fetched).1
      have limit := program.fetchBound
      omega
  apply WP.spec_mono (step_memory_store_core memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point machine.typed)
  intro out effect
  obtain ⟨samePlatform,stores,extension,mutation,pc,fields,operation⟩ := effect
  refine ⟨samePlatform,mutation,stores,extension,?_⟩
  rcases operation with ⟨success,g,represented,retained,fresh,metadata,transition,simulation⟩ | ⟨failed,sameStore,trace⟩
  · have covered : Abs.CoreState ⟨Store.decodeStore view code out.2.2.1,ambient,g::rest,[]⟩ := by
      rcases transition with same | step
      · rw [← same]; exact machine.core
      · exact Abs.Core.step_core _ _ machine.typed.typed machine.core step
    have preserved : SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val := by
      rw [fields]; exact .refl _ _
    have untouched : {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} := by rw [fields]
    exact Or.inl ⟨success,pc,g,CoreExecution.ordinary view code ambient {f with code := op.source argument::after} g rest expected raw.pc.val false machine
      stores extension raw index pc last frameFound program (.ready retained) represented ⟨metadata.address,metadata.module,metadata.results,metadata.locals⟩ untouched preserved fresh covered,simulation,core_owned_transition machine.typed machine.core transition,core_bound_transition machine.typed machine.core transition⟩
  · exact Or.inr ⟨failed,sameStore,trace⟩

end Exec.Interp.MemoryDescriptor
