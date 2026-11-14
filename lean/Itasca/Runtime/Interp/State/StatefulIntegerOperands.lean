import Itasca.Runtime.Interp.State.TableSource
import Itasca.Runtime.Interp.Memory.MemorySize
import Itasca.Runtime.SourceMachine.Stateful.Bound
import Itasca.Runtime.Interp.Relations.SourceClosure
import Itasca.Runtime.Interp.Relations.ReferenceSource
import Itasca.Runtime.Spec.FloatPromote
import Itasca.Runtime.Interp.Relations.Regions

/-!
Sections, each formerly its own module: StatefulSlots, StatefulOperandSlots, TableGrow, StatefulReferenceValue, StatefulOperandValues, StatefulIntegerOperands.
-/

/-! ## StatefulSlots -/

section

/-!
Slot effects for read-only store and reference instructions. Memory/table size, table get and reference operators share the concrete result-write argument while retaining their distinct source effects.
-/

/-! ## Stateful Reads -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem stateful_table_size_effect (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.execute_table_size memory exec store instanceIndex base dst table ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 object.elements.len)) ∧
      SourceMachine.Stateful.Transition state f rest after (.tableSize table.val)
        (SourceMachine.advance state {f with code := after,vals := f.vals++[SourceMachine.integerVal .I32 object.elements.length]} rest) ⦄ := by
  apply WP.spec_mono (table_size_effect memory exec store instanceIndex base dst table inst address object found mapped issued dstBound)
  intro out effect
  refine ⟨effect.1,effect.2.1,effect.2.2,{},trivial,?_⟩
  simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableSize,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,issued,decodeTable,alloc.vec.Vec.length]

theorem stateful_memory_size_effect (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (code : CodeInterpretation) (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.execute_memory_size memory exec store instanceIndex base dst ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ pages : Usize,
        pages.val = (view object.buf).length / 65536 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 pages)) ∧
        SourceMachine.Stateful.Transition state f rest after .memorySize
          (SourceMachine.advance state {f with code := after,vals := f.vals++[SourceMachine.integerVal .I32 pages.val]} rest) ⦄ := by
  apply WP.spec_mono (memory_size_handler memory view laws exec store instanceIndex base dst inst address object found mapped issued dstBound)
  intro out effect
  obtain ⟨success,same,pages,pagesEq,slots⟩ := effect
  refine ⟨success,same,pages,pagesEq,slots,{},trivial,?_⟩
  simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.memorySize,moduleEq,sourceStore,decodeInstance,decodeStore,
    List.getElem?_map,mapped,issued,decodeMemory,decodeBytes,pagesEq]

theorem stateful_table_get_effect (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst index table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length) (dstBound : base.val+dst.val < exec.slots.length)
    (sourceStore : state.store = decodeStore view code store) (moduleEq : f.module = decodeInstance store inst)
    (values : f.vals = front++[SourceMachine.integerVal .I32 position.val]) :
    runtime.interp.execute_table_get memory exec store instanceIndex base dst index table ⦃ out =>
      if position.val < object.elements.length then
        out.1 = .Ok () ∧ out.2.2 = store ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) object.elements.val[position.val]!) ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGet table.val)
          (SourceMachine.advance state {f with code := after,vals := front++[val_ref (decodeRef object.ty object.elements.val[position.val]!)]} rest)
      else out = (.Err (.Trap .TableOutOfBounds),exec,store) ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGet table.val) .trap ⦄ := by
  have decoded : SourceMachine.integer .I32 (SourceMachine.integerVal .I32 position.val) = some position.val :=
    SourceMachine.integer_accepts .I32 position.val (by change position.val < 2^32; scalar_tac)
  apply WP.spec_mono (table_get_effect memory exec store instanceIndex base dst index table inst address object position found mapped issued input indexBound dstBound)
  intro out effect
  by_cases inside : position.val < object.elements.length
  · simp only [inside,ite_true] at effect ⊢
    refine ⟨effect.1,effect.2.1,effect.2.2,{},trivial,?_⟩
    simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableGet,values,SourceMachine.pop_append,decoded,moduleEq,sourceStore,
      decodeInstance,decodeStore,List.getElem?_map,mapped,issued,decodeTable,inside,alloc.vec.Vec.length]
  · simp only [inside,ite_false] at effect ⊢
    refine ⟨effect,{},trivial,?_⟩
    simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.tableGet,values,SourceMachine.pop_append,decoded,moduleEq,sourceStore,
      decodeInstance,decodeStore,List.getElem?_map,mapped,issued,decodeTable,inside,alloc.vec.Vec.length]
end Itasca.Runtime.Interp

end

/-! ## Stateful Reference -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem stateful_ref_null_effect (exec : runtime.interp.Execution) (base : Usize) (dst : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (slotBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_null exec base dst ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) 0#u64) ∧
      SourceMachine.Stateful.Transition state f rest after (.refNull (decodeElemType type))
        (SourceMachine.advance state {f with code := after,vals := f.vals++[.REF_NULL (decodeElemType type)]} rest) ⦄ := by
  apply WP.spec_mono (ref_null_effect exec base dst slotBound)
  intro out effect
  exact ⟨effect.1,effect.2,{},trivial,rfl⟩

theorem stateful_ref_func_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst func : U32) (inst : runtime.store.ModuleInst) (address : runtime.FuncAddr)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.funcs.val[func.val]? = some address) (issued : address.index.val < store.funcs.length)
    (slotBound : base.val+dst.val < exec.slots.length)
    (moduleEq : f.module = decodeInstance store inst) :
    runtime.interp.execute_ref_func memory exec store instanceIndex base dst func ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ word : U64,
        word.val = address.index.val+1 ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) word) ∧
        SourceMachine.Stateful.Transition state f rest after (.refFunc func.val)
          (SourceMachine.advance state {f with code := after,vals := f.vals++[.REF_FUNC_ADDR address.index.val]} rest) ⦄ := by
  have addressBound : address.index.val < U64.max := by
    have bound := store.funcs.property
    rcases Usize.bounds_eq with h | h <;> scalar_tac
  apply WP.spec_mono (ref_func_effect memory exec store instanceIndex base dst func inst address found mapped addressBound slotBound)
  intro out effect
  obtain ⟨success,same,word,wordEq,slots⟩ := effect
  refine ⟨success,same,word,wordEq,slots,{},trivial,?_⟩
  simp [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.refFunc,moduleEq,decodeInstance,List.getElem?_map,mapped]

theorem stateful_ref_is_null_effect (exec : runtime.interp.Execution) (base : Usize) (dst src : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val)
    (values : f.vals = front++[val_ref (decodeRef type exec.slots.val[base.val+src.val]!)])
    (sourceBound : base.val+src.val < exec.slots.length) (destinationBound : base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_is_null exec base dst src ⦃ out =>
      out.1 = .Ok () ∧ ∃ word : U64,
        word.val = Spec.referenceIsNull (decodeRef type exec.slots.val[base.val+src.val]!) ∧
        SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) word) ∧
        SourceMachine.Stateful.Transition state f rest after .refIsNull
          (SourceMachine.advance state {f with code := after,vals := front++[SourceMachine.integerVal .I32 word.val]} rest) ⦄ := by
  apply WP.spec_mono (ref_is_null_effect exec base dst src sourceBound destinationBound)
  intro out effect
  let word : U64 := if exec.slots.val[base.val+src.val]! = 0#u64 then 1#u64 else 0#u64
  have wordEq : word.val = Spec.referenceIsNull (decodeRef type exec.slots.val[base.val+src.val]!) := by
    rw [decode_ref_is_null]
    dsimp only [word]
    split <;> rfl
  refine ⟨effect.1,word,wordEq,effect.2,{},trivial,?_⟩
  simp only [SourceMachine.Stateful.evaluate,SourceMachine.Stateful.refIsNull,values,SourceMachine.pop_append,SourceMachine.Stateful.as_reference_value,wordEq]
end Itasca.Runtime.Interp

end

/-! ## Stateful Slots -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem frame_write_result {exec out : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {after : List instr} {dst : U32} {word : U64} {value : val}
    (slots : FrameSlots exec raw f) (values : f.vals = front++consumed)
    (position : dst.val = Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (written : SlotsEffect exec out (exec.slots.val.set (raw.base.val+dst.val) word))
    (encoded : Compiler.encodeValue value = [word.val]) :
    FrameSlots out raw {f with code := after,vals := front++[value]} := by
  have livePrefix : ValuesAt exec.slots.val raw.base.val (f.locals++front) := by
    apply ValuesAt.locals (values := consumed)
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have offset : dst.val = (Compiler.encodeValues (f.locals++front)).length := by
    simp only [Compiler.encode_values_length,List.map_append,Compiler.slots_append,position]
  have result := WordsAt.set_append livePrefix word (by simpa only [←offset] using bound)
  change ValuesAt out.slots.val raw.base.val (f.locals++(front++[value]))
  rw [written.1]
  rw [offset]
  simpa only [ValuesAt,Compiler.encode_values_append,Compiler.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,encoded,List.append_assoc] using result
end Itasca.Runtime.Interp.Stateful

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem ref_null_slots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (f.vals.map Compiler.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_null exec raw.base dst ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) 0#u64) ∧
      FrameSlots out.2 raw {f with code:=after,vals:=f.vals++[.REF_NULL (decodeElemType type)]} ∧
      SourceMachine.Stateful.Transition state f rest after (.refNull (decodeElemType type))
        (SourceMachine.advance state {f with code:=after,vals:=f.vals++[.REF_NULL (decodeElemType type)]} rest) ⦄ := by
  apply WP.spec_mono (stateful_ref_null_effect exec raw.base dst type state f rest after bound)
  intro out effect
  exact ⟨effect.1,effect.2.1,frame_write_result (consumed := []) slots (by simp) position bound effect.2.1 rfl,effect.2.2⟩

theorem ref_func_slots (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst func : U32) (inst : runtime.store.ModuleInst) (address : runtime.FuncAddr)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.funcs.val[func.val]? = some address) (issued : address.index.val < store.funcs.length)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (f.vals.map Compiler.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_ref_func memory exec store raw.instance raw.base dst func ⦃ out =>
      out.1 = .Ok () ∧ out.2.2=store ∧ ∃ word : U64, word.val=address.index.val+1 ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[.REF_FUNC_ADDR address.index.val]} ∧
      SourceMachine.Stateful.Transition state f rest after (.refFunc func.val)
        (SourceMachine.advance state {f with code:=after,vals:=f.vals++[.REF_FUNC_ADDR address.index.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_ref_func_effect memory exec store raw.instance raw.base dst func inst address state f rest after found mapped issued bound moduleEq)
  intro out effect
  obtain ⟨success,same,word,wordEq,written,transition⟩ := effect
  exact ⟨success,same,word,wordEq,written,frame_write_result (consumed := []) slots (by simp) position bound written (by simp [Compiler.encodeValue,wordEq]),transition⟩

theorem table_size_slots (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst table : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (f.vals.map Compiler.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_table_size memory exec store raw.instance raw.base dst table ⦃ out =>
      out.1=.Ok () ∧ out.2.2=store ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 object.elements.len)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[SourceMachine.integerVal .I32 object.elements.length]} ∧
      SourceMachine.Stateful.Transition state f rest after (.tableSize table.val)
        (SourceMachine.advance state {f with code:=after,vals:=f.vals++[SourceMachine.integerVal .I32 object.elements.length]} rest) ⦄ := by
  apply WP.spec_mono (stateful_table_size_effect memory view code exec store raw.instance raw.base dst table inst address object state f rest after found mapped issued bound sourceStore moduleEq)
  intro out effect
  refine ⟨effect.1,effect.2.1,effect.2.2.1,frame_write_result (consumed := []) slots (by simp) position bound effect.2.2.1 ?_,effect.2.2.2⟩
  simp [Compiler.encodeValue,SourceMachine.integerVal,numtype_Inn,alloc.vec.Vec.length]

theorem memory_size_slots (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (f.vals.map Compiler.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_memory_size memory exec store raw.instance raw.base dst ⦃ out =>
      out.1=.Ok () ∧ out.2.2=store ∧ ∃ pages : Usize, pages.val=(view object.buf).length/65536 ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 pages)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[SourceMachine.integerVal .I32 pages.val]} ∧
      SourceMachine.Stateful.Transition state f rest after .memorySize
        (SourceMachine.advance state {f with code:=after,vals:=f.vals++[SourceMachine.integerVal .I32 pages.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_memory_size_effect memory view laws code exec store raw.instance raw.base dst inst address object state f rest after found mapped issued bound sourceStore moduleEq)
  intro out effect
  obtain ⟨success,same,pages,pagesEq,written,transition⟩ := effect
  refine ⟨success,same,pages,pagesEq,written,frame_write_result (consumed := []) slots (by simp) position bound written ?_,transition⟩
  simp [Compiler.encodeValue,SourceMachine.integerVal,numtype_Inn]
end Itasca.Runtime.Interp.Stateful

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

theorem frame_read_word {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front : List val} {value : val} {bits : Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++[value])
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValue value=[bits]) :
    raw.base.val+src.val < exec.slots.length ∧ exec.slots.val[raw.base.val+src.val]!.val=bits := by
  have words : WordsAt exec.slots.val raw.base.val (Compiler.encodeValues (f.locals++front)++[bits]) := by
    simpa only [FrameSlots,ValuesAt,values,Compiler.encode_values_append,Compiler.encodeValues,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,encoded,List.append_assoc] using slots
  have last := words.append_right 0 (by simp)
  simpa only [Compiler.encode_values_length,List.map_append,Compiler.slots_append,←position,Nat.add_zero,
    List.getElem!_cons_zero] using last

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem table_get_slots (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst table : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame) (after : List instr) (front : List val) (index : U32)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals=front++[SourceMachine.integerVal .I32 index.val])
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_table_get memory exec store raw.instance raw.base dst dst table ⦃ out =>
      if index.val < object.elements.length then
        out.1=.Ok () ∧ out.2.2=store ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) object.elements.val[index.val]!) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[val_ref (decodeRef object.ty object.elements.val[index.val]!)]} ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGet table.val)
          (SourceMachine.advance state {f with code:=after,vals:=front++[val_ref (decodeRef object.ty object.elements.val[index.val]!)]} rest)
      else out=(.Err (.Trap .TableOutOfBounds),exec,store) ∧
        SourceMachine.Stateful.Transition state f rest after (.tableGet table.val) .trap ⦄ := by
  obtain ⟨bound,wordEq⟩ := frame_read_word slots values position (by rfl)
  have actual : UScalar.cast .U32 exec.slots.val[raw.base.val+dst.val]! = index := by scalar_tac
  apply WP.spec_mono (stateful_table_get_effect memory view code exec store raw.instance raw.base dst dst table inst address object index state f rest after front found mapped issued actual bound bound sourceStore moduleEq values)
  intro out effect
  split at effect
  · rename_i inside
    rw [if_pos inside]
    refine ⟨effect.1,effect.2.1,effect.2.2.1,frame_write_result slots values position bound effect.2.2.1 ?_,effect.2.2.2⟩
    have encoded := encode_decoded_ref object.ty object.elements.val[index.val]!
    exact encoded
  · rename_i outside
    rw [if_neg outside]
    exact effect

theorem ref_is_null_slots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val)
    (slots : FrameSlots exec raw f)
    (values : f.vals=front++[val_ref (decodeRef type exec.slots.val[raw.base.val+dst.val]!)])
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.execute_ref_is_null exec raw.base dst dst ⦃ out =>
      out.1=.Ok () ∧ ∃ word : U64,
        word.val=Spec.referenceIsNull (decodeRef type exec.slots.val[raw.base.val+dst.val]!) ∧
        SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
        FrameSlots out.2 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} ∧
        SourceMachine.Stateful.Transition state f rest after .refIsNull
          (SourceMachine.advance state {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} rest) ⦄ := by
  have encoded := encode_decoded_ref type exec.slots.val[raw.base.val+dst.val]!
  have bound := (frame_read_word slots values position encoded).1
  apply WP.spec_mono (stateful_ref_is_null_effect exec raw.base dst dst type state f rest after front values bound bound)
  intro out effect
  obtain ⟨success,word,wordEq,written,transition⟩ := effect
  exact ⟨success,word,wordEq,written,frame_write_result slots values position bound written rfl,transition⟩
end Itasca.Runtime.Interp.Stateful

end

end

/-! ## StatefulOperandSlots -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem frame_consume {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} (after : List instr)
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed) :
    FrameSlots exec raw {f with code:=after,vals:=front} := by
  apply ValuesAt.locals (values := consumed)
  simpa only [FrameSlots,values,List.append_assoc] using slots

theorem frame_read_suffix {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValues consumed=bits) :
    WordsAt exec.slots.val (raw.base.val+src.val) bits := by
  have words : WordsAt exec.slots.val raw.base.val (Compiler.encodeValues (f.locals++front)++bits) := by
    simpa only [FrameSlots,ValuesAt,values,Compiler.encode_values_append,encoded,List.append_assoc] using slots
  simpa only [Compiler.encode_values_length,List.map_append,Compiler.slots_append,←position] using words.append_right

theorem frame_read_suffix_word {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValues consumed=bits) (index : Nat) (bound : index<bits.length) :
    raw.base.val+src.val+index<exec.slots.length ∧
    exec.slots.val[raw.base.val+src.val+index]!.val=bits[index]! :=
  frame_read_suffix slots values position encoded index bound
end Itasca.Runtime.Interp.Stateful

end

/-! ## TableGrow -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- Exact table-grow operand marshalling and result-slot update. The supplied
postcondition is solely the result of the called generic store primitive. -/
theorem table_grow_handler {M A : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (reference amount : U64)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (referenceSlot : exec.slots.val[base.val+dst.val]? = some reference)
    (amountSlot : exec.slots.val[base.val+dst.val+1]? = some amount)
    (post : U32 × runtime.store.Store M → Prop)
    (grown : runtime.store.Store.grow_table_index memory allocator store address.index (UScalar.cast .U32 amount) reference ⦃ post ⦄) :
    runtime.interp.execute_table_grow memory allocator exec store instanceIndex base dst table ⦃ out =>
      ∃ result, out.1 = .Ok () ∧ post (result,out.2.2) ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (base.val+dst.val) (UScalar.cast .U64 result)) ⦄ := by
  have refBound := (List.getElem?_eq_some_iff.mp referenceSlot).1
  have amountBound := (List.getElem?_eq_some_iff.mp amountSlot).1
  unfold runtime.interp.execute_table_grow
  rw [alloc.vec.Vec.index_slice_index]
  step with vec_index_given store.instances instanceIndex inst found as ⟨actual,instEq⟩
  subst actual
  simp only [lift,bind_ok]
  step with vec_index_given inst.tables (UScalar.cast .Usize table) address (by simpa only [U32.cast_Usize_val_eq] using mapped) as ⟨actual,addressEq⟩
  subst actual
  step as ⟨slot,slotEq⟩
  have slotValue : slot.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slotEq
  step with vec_index_given exec.slots slot reference (by simpa only [slotValue] using referenceSlot) as ⟨word,wordEq⟩
  subst word
  step as ⟨slot2,slot2Eq⟩
  have slot2Value : slot2.val = base.val+dst.val := by simpa only [U32.cast_Usize_val_eq] using slot2Eq
  step as ⟨nextSlot,nextEq⟩
  have nextValue : nextSlot.val = base.val+dst.val+1 := by simpa only [slot2Value] using nextEq
  step with vec_index_given exec.slots nextSlot amount (by simpa only [nextValue] using amountSlot) as ⟨word,wordEq⟩
  subst word
  step with grown as ⟨result,nextStore,growth⟩
  step* <;> simp_all [SlotsEffect]
  exact ⟨result,growth,rfl⟩
end Itasca.Runtime.Interp

end

/-! ## StatefulReferenceValue -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem reference_word_value (value : val) (type : Itasca.wasm_types.ElemType) (word : U64)
    (typed : Compiler.valueType value=valtype_reftype (Store.decodeElemType type))
    (encoded : Compiler.encodeValue value=[word.val]) :
    value=val_ref (Store.decodeRef type word) := by
  cases value with
  | CONST ty bits => cases ty <;> cases type <;> simp [Compiler.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | VCONST ty bits => cases type <;> simp [Compiler.valueType,Store.decodeElemType,valtype_reftype,valtype_numtype] at typed
  | REF_NULL reference =>
    cases reference <;> cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
  | REF_FUNC_ADDR index =>
    cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
  | REF_HOST_ADDR index =>
    cases type <;> simp_all [Compiler.valueType,Compiler.encodeValue,Store.decodeElemType,valtype_reftype,Store.decodeRef,val_ref]
    all_goals simp [←encoded]
theorem reference_encoding (reference : ref) : ∃ bits, Compiler.encodeValue (val_ref reference) = [bits] := by
  cases reference <;> exact ⟨_,rfl⟩

theorem ref_is_null_value_slots
    (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.wasm_types.ElemType) (state : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (front : List val) (reference : ref)
    (slots : FrameSlots exec raw f) (values : f.vals=front++[val_ref reference])
    (referenceType : Compiler.valueType (val_ref reference)=valtype_reftype (Store.decodeElemType type))
    (position : dst.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    runtime.interp.execute_ref_is_null exec raw.base dst dst ⦃ out =>
      out.1=.Ok () ∧ ∃ word : U64, word.val=Spec.referenceIsNull reference ∧
        SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
        FrameSlots out.2 raw {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} ∧
        SourceMachine.Stateful.Transition state f rest after .refIsNull
          (SourceMachine.advance state {f with code:=after,vals:=front++[SourceMachine.integerVal .I32 word.val]} rest) ⦄ := by
  obtain ⟨bits,encoded⟩ := reference_encoding reference
  have wordEq := (frame_read_word slots values position encoded).2
  have same := reference_word_value (val_ref reference) type exec.slots.val[raw.base.val+dst.val]! referenceType (by rw [wordEq]; exact encoded)
  have referenceEq : reference=Store.decodeRef type exec.slots.val[raw.base.val+dst.val]! := by
    have equality := congrArg SourceMachine.Stateful.asReference same
    simpa only [SourceMachine.Stateful.as_reference_value,Option.some.injEq] using equality
  have decodedValues : f.vals=front++[val_ref (Store.decodeRef type exec.slots.val[raw.base.val+dst.val]!)] := by rw [←referenceEq]; exact values
  apply WP.spec_mono (ref_is_null_slots exec raw dst type state f rest after front slots decodedValues position)
  intro out effect
  simpa only [←referenceEq] using effect
end Itasca.Runtime.Interp.Stateful

end

/-! ## StatefulOperandValues -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

theorem two_operand_values {operands : List val} {left right : valtype}
    (types : operands.map Compiler.valueType=[left,right]) :
    ∃ x y,operands=[x,y] ∧ Compiler.valueType x=left ∧ Compiler.valueType y=right := by
  cases operands with
  | nil => simp at types
  | cons x xs =>
    cases xs with
    | nil => simp at types
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at types
      exact ⟨x,y,by rw [types.2.2],types.1,types.2.1⟩

theorem three_operand_values {operands : List val} {first second third : valtype}
    (types : operands.map Compiler.valueType=[first,second,third]) :
    ∃ x y z,operands=[x,y,z] ∧ Compiler.valueType x=first ∧ Compiler.valueType y=second ∧ Compiler.valueType z=third := by
  cases operands with
  | nil => simp at types
  | cons x xs =>
    have firstEq : Compiler.valueType x=first := (List.cons.inj types).1
    obtain ⟨y,z,rfl,secondEq,thirdEq⟩ := two_operand_values (List.cons.inj types).2
    exact ⟨x,y,z,rfl,firstEq,secondEq,thirdEq⟩

theorem frame_reference_second {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front : List val} {firstValue : val} {bits : Nat} {reference : ref}
    {first second : U32} {type : Itasca.wasm_types.ElemType}
    (slots : FrameSlots exec raw f) (values : f.vals=front++[firstValue,val_ref reference])
    (prefixBits : Compiler.encodeValue firstValue=[bits])
    (referenceType : Compiler.valueType (val_ref reference)=valtype_reftype (decodeElemType type))
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (secondSlot : second.val=first.val+1) :
    val_ref reference=val_ref (decodeRef type exec.slots.val[raw.base.val+second.val]!) := by
  obtain ⟨referenceBits,encoded⟩ := reference_encoding reference
  have suffix : Compiler.encodeValues [firstValue,val_ref reference]=[bits,referenceBits] := by
    simp [Compiler.encodeValues,prefixBits,encoded]
  obtain ⟨bound,word⟩ := frame_read_suffix_word slots values position suffix 1 (by simp)
  have wordEq : exec.slots.val[raw.base.val+second.val]!.val=referenceBits := by
    simpa [secondSlot,Nat.add_assoc] using word
  exact reference_word_value _ _ _ referenceType (by rw [wordEq];exact encoded)
theorem frame_read_scalar {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front consumed : List val} {bits : List Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++consumed)
    (position : src.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType))
    (encoded : Compiler.encodeValues consumed=bits) (index : Nat) (bound : index<bits.length)
    (word : U64) (wordValue : word.val=bits[index]!) :
    exec.slots.val[raw.base.val+src.val+index]?=some word := by
  obtain ⟨fits,actual⟩ := frame_read_suffix_word slots values position encoded index bound
  have equal : exec.slots.val[raw.base.val+src.val+index]! = word := by scalar_tac
  rw [List.getElem?_eq_getElem fits]
  rw [←_root_.getElem!_pos exec.slots.val (raw.base.val+src.val+index) fits,equal]
end Itasca.Runtime.Interp.Stateful

end

/-! ## StatefulIntegerOperands -/

section

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt

theorem three_i32_operands (store : _root_.store) (operands : List val)
    (types : operands.map Compiler.valueType=[.I32,.I32,.I32])
    (typed : ∀ value∈operands,Val_ok store value (Compiler.valueType value)) :
    ∃ x y z : U32,operands=[SourceMachine.integerVal .I32 x.val,SourceMachine.integerVal .I32 y.val,SourceMachine.integerVal .I32 z.val] := by
  obtain ⟨x,y,z,rfl,xType,yType,zType⟩ := three_operand_values types
  have xTyped := typed x (by simp)
  have yTyped := typed y (by simp)
  have zTyped := typed z (by simp)
  rw [xType] at xTyped
  rw [yType] at yTyped
  rw [zType] at zTyped
  obtain ⟨a,rfl,aBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) xTyped
  obtain ⟨b,rfl,bBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) yTyped
  obtain ⟨c,rfl,cBound⟩ := SourceMachine.integer_val_inv (ty:=.I32) zTyped
  exact ⟨UScalar.ofNatCore a aBound,UScalar.ofNatCore b bBound,UScalar.ofNatCore c cBound,rfl⟩

theorem frame_three_i32_slots {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : SourceMachine.AFrame} {front : List val} {first : U32} (a b c : U32)
    (slots : FrameSlots exec raw f)
    (values : f.vals=front++[SourceMachine.integerVal .I32 a.val,SourceMachine.integerVal .I32 b.val,SourceMachine.integerVal .I32 c.val])
    (position : first.val=Compiler.slots (f.locals.map Compiler.valueType)+Compiler.slots (front.map Compiler.valueType)) :
    exec.slots.val[raw.base.val+first.val]?=some (UScalar.cast .U64 a) ∧
    exec.slots.val[raw.base.val+first.val+1]?=some (UScalar.cast .U64 b) ∧
    exec.slots.val[raw.base.val+first.val+2]?=some (UScalar.cast .U64 c) := by
  have encoded : Compiler.encodeValues [SourceMachine.integerVal .I32 a.val,SourceMachine.integerVal .I32 b.val,SourceMachine.integerVal .I32 c.val]=[a.val,b.val,c.val] := rfl
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_zero] using frame_read_scalar slots values position encoded 0 (by simp) (UScalar.cast .U64 a) (by simp)
  · exact frame_read_scalar slots values position encoded 1 (by simp) (UScalar.cast .U64 b) (by simp)
  · exact frame_read_scalar slots values position encoded 2 (by simp) (UScalar.cast .U64 c) (by simp)
end Itasca.Runtime.Interp.Stateful

end
