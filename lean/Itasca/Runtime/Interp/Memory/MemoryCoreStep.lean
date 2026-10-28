import Itasca.Runtime.Interp.Memory.MemoryCoreStore
import Itasca.Runtime.Abs.Core.MemoryLoad
import Itasca.Runtime.Abs.Core.MemoryStore
namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
 theorem execute_load_core_simulation_exact {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_load memory exec store raw.instance raw.base (loadOpcode op) address address offset ⦃ out =>
      (∃ nextFrame, out.1 = .Ok () ∧
        Abs.Core.load initial f rest after op argument = .next {initial with frames := nextFrame :: rest} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2 raw nextFrame ∧ {out.2 with slots := exec.slots} = exec) ∨
      (out = (.Err (.Trap .MemoryOutOfBounds),exec) ∧ ∃ n, 0 < n ∧
        StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩) ⦄ := by
  dsimp only
  have source := Abs.Core.load_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_load_core memory view laws code exec store raw op address offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits argument found mapped issued rfl moduleEq values slots addressSlot bitsBound offsetEq)
  intro out effect
  rcases effect with ⟨nextFrame,success,actual,slotsAfter,unchanged⟩ | ⟨failed,actual⟩
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨nextFrame,success,actual,fresh,step,slotsAfter,unchanged⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,trace⟩
 theorem step_load_core_simulation {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Load) (address offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (bitsBound : bits < 2^32) (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.memoryLoadInstruction op address address offset))
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.1 = store ∧ out.2.2.2 = platform ∧
      (      (∃ nextFrame, out.1 = .Ok () ∧
        Abs.Core.load initial f rest after op argument = .next {initial with frames := nextFrame :: rest} ∧
        Abs.CoreTyped {initial with frames := nextFrame :: rest} ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set index {raw with pc := pc}})) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧ ∃ n, 0 < n ∧
        StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Code.memoryLoadInstruction op address address offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have handler := execute_load_core_simulation_exact memory view laws code {exec with frames := exec.frames.set index {raw with pc := pc}} store raw op address offset inst memoryAddress object ambient f rest after front bits argument found mapped issued moduleEq values slots addressSlot bitsBound offsetEq typed
  apply WP.spec_mono (dispatch_load memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address address offset handler)
  intro out effect
  refine ⟨effect.2.1,effect.2.2,?_⟩
  rcases effect.1 with ⟨nextFrame,success,actual,fresh,source,represented,unchanged⟩ | ⟨failed,trace⟩
  · exact Or.inl ⟨nextFrame,success,actual,fresh,source,represented,pc,pcNext,unchanged⟩
  · exact Or.inr ⟨congrArg Prod.fst failed,⟨pc,pcNext,congrArg Prod.snd failed⟩,trace⟩
 theorem execute_store_core_simulation_exact {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.execute_store memory exec store raw.instance raw.base (storeOpcode op) address value offset ⦃ out =>
      MemoryMutation view store out.2 memoryAddress object ∧
      ((out.1 = .Ok () ∧
        Abs.Core.store initial f rest after op argument = .next {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2, frames := {f with code := after,vals := front} :: rest}) ∧
        FrameSlots exec raw {f with code := after,vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩)) ⦄ := by
  dsimp only
  have source := Abs.Core.store_progress (Store.decodeStore view code store) ambient f rest after op argument typed
  apply WP.spec_mono (execute_store_core_values memory view laws code exec store raw op address value offset inst memoryAddress object
    ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩ f rest after front bits number argument found mapped issued rfl moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq)
  intro out effect
  refine ⟨effect.1,?_⟩
  rcases effect.2 with ⟨success,actual,slotsAfter⟩ | ⟨failed,actual,unchanged⟩
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      cases abstract
      exact Or.inl ⟨success,actual,fresh,extension,step,slotsAfter⟩
    · rw [actual] at trapped
      contradiction
  · rcases source with ⟨next,abstract,fresh,extension,step⟩ | ⟨trapped,trace⟩
    · rw [actual] at abstract
      contradiction
    · exact Or.inr ⟨failed,unchanged,trace⟩
 theorem step_store_core_simulation {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
    (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
    (allocator : runtime.platform.Alloc A) (platform : P) (index : Usize)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (op : Abs.Memory.Store) (address value offset : U32) (inst : runtime.store.ModuleInst)
    (memoryAddress : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (ambient : frame) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (front : List val) (bits : Nat) (number : num_) (argument : memarg)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some memoryAddress)
    (issued : store.memories.val[memoryAddress.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (values : f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number])
    (slots : FrameSlots exec raw f)
    (addressSlot : address.val = Code.slots (f.locals.map Code.valueType) + Code.slots (front.map Code.valueType))
    (valueSlot : value.val = address.val+1)
    (bitsBound : bits < 2^32) (numberWf : wf_num_ op.type number)
    (offsetEq : proj_uN_0 argument.OFFSET = offset.val)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : index.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[index.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Code.memoryStoreInstruction op address value offset))
    (pcBound : raw.pc.val < U32.max)
    (typed : Abs.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩) :
    let initial : Abs.AState := ⟨Store.decodeStore view code store,ambient,{f with code := op.source argument :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set index {raw with pc := pc}}) ∧
      (      MemoryMutation view store out.2.2.1 memoryAddress object ∧
      ((out.1 = .Ok () ∧
        Abs.Core.store initial f rest after op argument = .next {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest} ∧
        Abs.CoreTyped {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest} ∧
        Extend_store (Store.decodeStore view code store) (Store.decodeStore view code out.2.2.1) ∧
        StepH (Abs.decode initial) [] (Abs.decode {initial with store := Store.decodeStore view code out.2.2.1, frames := {f with code := after,vals := front} :: rest}) ∧
        FrameSlots exec raw {f with code := after,vals := front}) ∨
      (out.1 = .Err (.Trap .MemoryOutOfBounds) ∧ Store.decodeStore view code out.2.2.1 = Store.decodeStore view code store ∧
        ∃ n, 0 < n ∧ StepsHN n (Abs.decode initial) [] ⟨⟨Store.decodeStore view code store,ambient⟩,[.TRAP]⟩))) ⦄ := by
  dsimp only
  apply step_fetch memory hooks floats allocator exec store platform index raw inst compiled
    (Code.memoryStoreInstruction op address value offset) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  have handler := execute_store_core_simulation_exact memory view laws code {exec with frames := exec.frames.set index {raw with pc := pc}} store raw op address value offset inst memoryAddress object ambient f rest after front bits number argument found mapped issued moduleEq values slots addressSlot valueSlot bitsBound numberWf offsetEq typed
  apply WP.spec_mono (dispatch_store memory hooks floats allocator _ store platform index raw.instance raw.function raw.base op address value offset handler)
  intro out effect
  exact ⟨effect.2.2,⟨pc,pcNext,effect.2.1⟩,effect.1⟩
end Itasca.Runtime.Interp.MemoryDescriptor
