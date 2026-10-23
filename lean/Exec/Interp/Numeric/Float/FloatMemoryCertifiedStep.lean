import Exec.Interp.Numeric.Float.FloatPoint
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.Memory.MemoryCoreTransition
import Exec.Interp.Numeric.Float.FloatMemoryPrepare
import Exec.Interp.Memory.MemoryCoreStep
import Exec.Interp.Memory.MemoryCoreResult
import Exec.Interp.Memory.MemoryLoadStepFootprint
namespace Exec.Interp.FloatMemoryDescriptor
open Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Exec.Spec

theorem coreFramePoint_load_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (pcBound : raw.pc.val < U32.max)
    (point : FloatFramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FloatFramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((∃ nextFrame pc, out.1 = .Ok () ∧
        Abs.Core.step initial = .next {initial with frames := nextFrame :: rest} ∧ pc.val = raw.pc.val+1 ∧
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FloatFramePoint (Store.decodeStore view code store) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values}) ∧
        ∃ position word, raw.base.val ≤ position ∧ position < exec.slots.length ∧
          out.2.1.slots.val = exec.slots.val.set position word) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧
        (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_load_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,bits,memoryAddress,object,address,offset,values,bound,mapped,issued,heights,position,offsetEq,fetch,tail⟩ := operation
    obtain ⟨out,result,footprint⟩ := WP.spec_imp_exists (step_load_footprint memory hooks floats allocator platform index view laws code exec store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots position bound offsetEq compiled last frameFound codeFound fetch pcBound)
    have normal := (step_load_core_simulation memory hooks floats allocator platform index view laws code exec store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots position bound offsetEq compiled last frameFound codeFound fetch pcBound typed)
    rw [result] at normal ⊢
    apply WP.spec.ret
    have effect := normal
    rw [WP.spec_ok] at effect
    refine ⟨effect.1,effect.2.1,?_⟩
    rcases effect.2.2 with ⟨nextFrame,success,actual,fresh,source,represented,pc,pcNext,unchanged⟩ | trapped
    · obtain ⟨value,frameEq,valueType⟩ := core_load_next_shape view code store inst memoryAddress object _ f nextFrame rest after front bits op argument offset rfl moduleEq mapped issued values bound offsetEq actual
      refine Or.inl ⟨nextFrame,pc,success,(core_step_load_eq _ _ _ _ _ _ _).trans actual,pcNext,unchanged,fresh,source,represented,?_,⟨_,frameEq⟩,?_⟩
      · rw [frameEq]
        exact corePoint_load_continue point front bits value op.type after values heights valueType tail pc pcNext
      · obtain ⟨word,capacity,exactWords⟩ := footprint success
        exact ⟨raw.base.val+address.val,word,Nat.le_add_right _ _,capacity,exactWords⟩
    · exact Or.inr trapped

theorem coreFramePoint_store_step {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
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
    (pcBound : raw.pc.val < U32.max)
    (point : FloatFramePoint (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    (∃ target : U32, raw.pc.val < target.val ∧ compiled.code.val[raw.pc.val]? = some (.Jump target) ∧
      FloatFramePoint (Store.decodeStore view code store) {raw with pc := target} {f with code := op.source argument :: after} compiled C targets next output) ∨
    (runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧
      (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ∃ memoryAddress object, inst.memories.val[0]? = some memoryAddress ∧
        store.memories.val[memoryAddress.index.val]? = some object ∧
        MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((∃ nextFrame, out.1 = .Ok () ∧
        Abs.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 {raw with pc := pc} nextFrame ∧
        FloatFramePoint (Store.decodeStore view code out.2.2.1) {raw with pc := pc} nextFrame compiled C targets next output ∧
        (∃ values, nextFrame = {f with code := after,vals := values})) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩))) ⦄) := by
  dsimp only
  have frameTyped : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} [] := by
    cases typed.typed.frames with | cons head _ => exact head
  rcases coreFramePoint_store_prepare view code store inst raw f compiled C targets next output after op argument moduleEq frameTyped point with jump | operation
  · exact Or.inl jump
  · apply Or.inr
    obtain ⟨front,bits,number,memoryAddress,object,address,value,offset,values,bound,numberWf,mapped,issued,heights,position,valuePosition,offsetEq,fetch,tail⟩ := operation
    apply WP.spec_mono (step_store_core_simulation memory hooks floats allocator platform index view laws code exec store raw op address value offset inst memoryAddress object ambient f rest after front bits number argument found mapped issued moduleEq values slots position valuePosition bound numberWf offsetEq compiled last frameFound codeFound fetch pcBound typed)
    intro out effect
    obtain ⟨pc,pcNext,unchanged⟩ := effect.2.1
    refine ⟨effect.1,pc,pcNext,unchanged,memoryAddress,object,mapped,issued,effect.2.2.1,?_⟩
    rcases effect.2.2.2 with ⟨success,actual,fresh,extension,source,represented⟩ | trapped
    · refine Or.inl ⟨_,success,(core_step_store_eq _ _ _ _ _ _ _).trans actual,fresh,extension,source,?_,?_,⟨_,rfl⟩⟩
      · simpa only [unchanged,FrameSlots] using represented
      · exact corePoint_store_continue point extension front _ after values heights tail pc pcNext
    · exact Or.inr trapped

end Exec.Interp.FloatMemoryDescriptor
