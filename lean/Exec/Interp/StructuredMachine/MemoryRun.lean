import Exec.Interp.StructuredMachine.FloatHeads
import Exec.Code.Local.Lowering.Float.FloatCoreProjection
import Exec.Interp.StructuredMachine.MemoryCertifiedStep
import Exec.Interp.StructuredMachine.ForwardJump
import Exec.Spec.Extend
namespace Exec.Interp.StructuredMachine.Memory
variable {emission : FunctionEmission} [∀ compiled, FloatHeads (emission compiled)]
open Exec.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Exec.Spec
theorem step_memory_load_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      ((out.1 = .Ok () ∧ ∃ (pc : U32) (g : Abs.AFrame),
        {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission (Store.decodeStore view code store) {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with frames := g::rest} ∨ Abs.Core.step initial = .next {initial with frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial {initial with frames := g::rest} ∧
        (out.2.1.slots.val = exec.slots.val ∨ ∃ position word, raw.base.val ≤ position ∧
          position < exec.slots.length ∧ out.2.1.slots.val = exec.slots.val.set position word)) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ ∃ n, 0 < n ∧
        StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases coreFramePoint_load_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
      last frameFound found codeFound pcBound forward fetched slots tail typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    refine ⟨sameStore,samePlatform,Or.inl ⟨success,target,_,?_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation,?_⟩⟩
    · rw [exactState]
    · exact Or.inl (by rw [exactState])
  · apply WP.spec_mono operation
    intro out effect
    refine ⟨effect.1,effect.2.1,?_⟩
    rcases effect.2.2 with ⟨g,pc,success,actual,pcNext,unchanged,fresh,source,represented,retained,shape,footprint⟩ | ⟨failed,unchanged,trace⟩
    · have metadata : FrameMetadata f g := by obtain ⟨values,rfl⟩ := shape; exact ⟨rfl,rfl,rfl,rfl⟩
      refine Or.inl ⟨success,pc,g,unchanged,represented,retained,fresh,metadata,Or.inr actual,?_,Or.inr footprint⟩
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩
    · exact Or.inr ⟨failed,trace⟩

theorem step_memory_store_core {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (inst : runtime.store.Instance) (compiled : runtime.bytecode.CompiledFunction)
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
    (point : FramePoint emission (Store.decodeStore view code store) raw {f with code := op.source argument :: after} compiled C targets next output)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after}::rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ FrameStoreMetadata store out.2.2.1 ∧
      Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
      (out.2.2.1 = store ∨ ∃ memoryAddress object,
        store.memories.val[memoryAddress.index.val]? = some object ∧ MemoryMutation view store out.2.2.1 memoryAddress object) ∧
      ∃ pc : U32, out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}} ∧
      ((out.1 = .Ok () ∧ ∃ g : Abs.AFrame,
        FrameSlots out.2.1 {raw with pc := pc} g ∧
        FramePoint emission (Store.decodeStore view code out.2.2.1) {raw with pc := pc} g compiled C targets next output ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∧ FrameMetadata f g ∧
        (initial = {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest} ∨
          Abs.Core.step initial = .next {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∧
        ConcreteSim compiled.code.length raw.pc.val pc.val false false initial
          {initial with store := Store.decodeStore view code out.2.2.1,frames := g::rest}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  rcases coreFramePoint_store_step memory hooks floats allocator platform index view laws code exec store raw inst compiled
    ambient f rest after op argument C targets next output found moduleEq slots last frameFound codeFound pcBound point typed with jump | operation
  · obtain ⟨target,forward,fetched,tail⟩ := jump
    apply WP.spec_mono (step_forward_jump_flat memory hooks floats allocator exec store platform index raw inst compiled
      (Store.decodeStore view code store) ambient {f with code := op.source argument::after} rest C targets next output target
      last frameFound found codeFound pcBound forward fetched slots tail typed)
    intro out effect
    obtain ⟨success,sameStore,samePlatform,exactState,represented,retained,fresh,simulation⟩ := effect
    rw [sameStore]
    exact ⟨samePlatform,.refl store,extend_store_refl _ typed.typed.store,Or.inl rfl,target,exactState,
      Or.inl ⟨success,_,represented,retained,fresh,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,simulation⟩⟩
  · apply WP.spec_mono operation
    intro out effect
    obtain ⟨samePlatform,pc,pcNext,exactState,memoryAddress,object,mapped,issued,mutation,operation⟩ := effect
    rcases operation with ⟨g,success,actual,fresh,extension,source,represented,retained,shape⟩ | ⟨failed,unchanged,trace⟩
    · have metadata : FrameMetadata f g := by obtain ⟨values,rfl⟩ := shape; exact ⟨rfl,rfl,rfl,rfl⟩
      refine ⟨samePlatform,mutation.frame_metadata,extension,Or.inr ⟨_,_,issued,mutation⟩,pc,exactState,
        Or.inl ⟨success,g,represented,retained,fresh,metadata,Or.inr actual,?_⟩⟩
      exact Or.inr ⟨1,by omega,by simpa using StepsHN.cons source (StepsHN.refl (stepH_wf source).2)⟩
    · have extension : Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) := by
        rw [unchanged]
        exact extend_store_refl _ typed.typed.store
      exact ⟨samePlatform,mutation.frame_metadata,extension,Or.inr ⟨_,_,issued,mutation⟩,pc,exactState,Or.inr ⟨failed,unchanged,trace⟩⟩

end Exec.Interp.StructuredMachine.Memory
