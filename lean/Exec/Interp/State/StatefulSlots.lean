import Exec.Interp.State.StatefulReference
import Exec.Interp.State.StatefulReads
import Exec.Interp.Relations.Regions
namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std

theorem frame_write_result {exec out : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front consumed : List val} {after : List instr} {dst : U32} {word : U64} {value : val}
    (slots : FrameSlots exec raw f) (values : f.vals = front++consumed)
    (position : dst.val = Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (written : SlotsEffect exec out (exec.slots.val.set (raw.base.val+dst.val) word))
    (encoded : Code.encodeValue value = [word.val]) :
    FrameSlots out raw {f with code := after,vals := front++[value]} := by
  have livePrefix : ValuesAt exec.slots.val raw.base.val (f.locals++front) := by
    apply ValuesAt.locals (values := consumed)
    simpa only [FrameSlots,values,List.append_assoc] using slots
  have offset : dst.val = (Code.encodeValues (f.locals++front)).length := by
    simp only [Code.encodeValues_length,List.map_append,Code.slots_append,position]
  have result := WordsAt.set_append livePrefix word (by simpa only [←offset] using bound)
  change ValuesAt out.slots.val raw.base.val (f.locals++(front++[value]))
  rw [written.1]
  rw [offset]
  simpa only [ValuesAt,Code.encodeValues_append,Code.encodeValues,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,encoded,List.append_assoc] using result
end Itasca.Runtime.Interp.Stateful

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem ref_null_slots (exec : runtime.interp.Execution) (raw : runtime.interp.Frame) (dst : U32)
    (type : Itasca.types.ElemType) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots (f.locals.map Code.valueType)+Code.slots (f.vals.map Code.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length) :
    runtime.interp.execute_ref_null exec raw.base dst ⦃ out =>
      out.1 = .Ok () ∧ SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) 0#u64) ∧
      FrameSlots out.2 raw {f with code:=after,vals:=f.vals++[.REF_NULL (decodeElemType type)]} ∧
      Abs.Stateful.Transition state f rest after (.refNull (decodeElemType type))
        (Abs.advance state {f with code:=after,vals:=f.vals++[.REF_NULL (decodeElemType type)]} rest) ⦄ := by
  apply WP.spec_mono (stateful_ref_null_effect exec raw.base dst type state f rest after bound)
  intro out effect
  exact ⟨effect.1,effect.2.1,frame_write_result (consumed := []) slots (by simp) position bound effect.2.1 rfl,effect.2.2⟩

theorem ref_func_slots (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (raw : runtime.interp.Frame) (dst func : U32) (inst : runtime.store.ModuleInst) (address : runtime.FuncAddr)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.funcs.val[func.val]? = some address) (issued : address.index.val < store.funcs.length)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots (f.locals.map Code.valueType)+Code.slots (f.vals.map Code.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_ref_func memory exec store raw.instance raw.base dst func ⦃ out =>
      out.1 = .Ok () ∧ out.2.2=store ∧ ∃ word : U64, word.val=address.index.val+1 ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[.REF_FUNC_ADDR address.index.val]} ∧
      Abs.Stateful.Transition state f rest after (.refFunc func.val)
        (Abs.advance state {f with code:=after,vals:=f.vals++[.REF_FUNC_ADDR address.index.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_ref_func_effect memory exec store raw.instance raw.base dst func inst address state f rest after found mapped issued bound moduleEq)
  intro out effect
  obtain ⟨success,same,word,wordEq,written,transition⟩ := effect
  exact ⟨success,same,word,wordEq,written,frame_write_result (consumed := []) slots (by simp) position bound written (by simp [Code.encodeValue,wordEq]),transition⟩

theorem table_size_slots (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst table : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots (f.locals.map Code.valueType)+Code.slots (f.vals.map Code.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_table_size memory exec store raw.instance raw.base dst table ⦃ out =>
      out.1=.Ok () ∧ out.2.2=store ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 object.elements.len)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[Abs.integerVal .I32 object.elements.length]} ∧
      Abs.Stateful.Transition state f rest after (.tableSize table.val)
        (Abs.advance state {f with code:=after,vals:=f.vals++[Abs.integerVal .I32 object.elements.length]} rest) ⦄ := by
  apply WP.spec_mono (stateful_table_size_effect memory view code exec store raw.instance raw.base dst table inst address object state f rest after found mapped issued bound sourceStore moduleEq)
  intro out effect
  refine ⟨effect.1,effect.2.1,effect.2.2.1,frame_write_result (consumed := []) slots (by simp) position bound effect.2.2.1 ?_,effect.2.2.2⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn,alloc.vec.Vec.length]

theorem memory_size_slots (view : M → Slice U8) (laws : Platform.MemoryLaws memory view) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst : U32) (inst : runtime.store.ModuleInst) (address : runtime.MemoryAddr) (object : runtime.store.MemInst M)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.memories.val[0]? = some address) (issued : store.memories.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Code.slots (f.locals.map Code.valueType)+Code.slots (f.vals.map Code.valueType))
    (bound : raw.base.val+dst.val < exec.slots.length)
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_memory_size memory exec store raw.instance raw.base dst ⦃ out =>
      out.1=.Ok () ∧ out.2.2=store ∧ ∃ pages : Usize, pages.val=(view object.buf).length/65536 ∧
      SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) (UScalar.cast .U64 pages)) ∧
      FrameSlots out.2.1 raw {f with code:=after,vals:=f.vals++[Abs.integerVal .I32 pages.val]} ∧
      Abs.Stateful.Transition state f rest after .memorySize
        (Abs.advance state {f with code:=after,vals:=f.vals++[Abs.integerVal .I32 pages.val]} rest) ⦄ := by
  apply WP.spec_mono (stateful_memory_size_effect memory view laws code exec store raw.instance raw.base dst inst address object state f rest after found mapped issued bound sourceStore moduleEq)
  intro out effect
  obtain ⟨success,same,pages,pagesEq,written,transition⟩ := effect
  refine ⟨success,same,pages,pagesEq,written,frame_write_result (consumed := []) slots (by simp) position bound written ?_,transition⟩
  simp [Code.encodeValue,Abs.integerVal,numtype_Inn]
end Itasca.Runtime.Interp.Stateful

namespace Itasca.Runtime.Interp.Stateful
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Store

theorem frame_read_word {exec : runtime.interp.Execution} {raw : runtime.interp.Frame}
    {f : Abs.AFrame} {front : List val} {value : val} {bits : Nat} {src : U32}
    (slots : FrameSlots exec raw f) (values : f.vals=front++[value])
    (position : src.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (encoded : Code.encodeValue value=[bits]) :
    raw.base.val+src.val < exec.slots.length ∧ exec.slots.val[raw.base.val+src.val]!.val=bits := by
  have words : WordsAt exec.slots.val raw.base.val (Code.encodeValues (f.locals++front)++[bits]) := by
    simpa only [FrameSlots,ValuesAt,values,Code.encodeValues_append,Code.encodeValues,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,encoded,List.append_assoc] using slots
  have last := words.append_right 0 (by simp)
  simpa only [Code.encodeValues_length,List.map_append,Code.slots_append,←position,Nat.add_zero,
    List.getElem!_cons_zero] using last

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem table_get_slots (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst table : U32) (inst : runtime.store.ModuleInst) (address : runtime.TableAddr) (object : runtime.store.TableInst)
    (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame) (after : List instr) (front : List val) (index : U32)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address) (issued : store.tables.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals=front++[Abs.integerVal .I32 index.val])
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType))
    (sourceStore : state.store=decodeStore view code store) (moduleEq : f.module=decodeInstance store inst) :
    runtime.interp.execute_table_get memory exec store raw.instance raw.base dst dst table ⦃ out =>
      if index.val < object.elements.length then
        out.1=.Ok () ∧ out.2.2=store ∧
        SlotsEffect exec out.2.1 (exec.slots.val.set (raw.base.val+dst.val) object.elements.val[index.val]!) ∧
        FrameSlots out.2.1 raw {f with code:=after,vals:=front++[val_ref (decodeRef object.ty object.elements.val[index.val]!)]} ∧
        Abs.Stateful.Transition state f rest after (.tableGet table.val)
          (Abs.advance state {f with code:=after,vals:=front++[val_ref (decodeRef object.ty object.elements.val[index.val]!)]} rest)
      else out=(.Err (.Trap .TableOutOfBounds),exec,store) ∧
        Abs.Stateful.Transition state f rest after (.tableGet table.val) .trap ⦄ := by
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
    (type : Itasca.types.ElemType) (state : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (front : List val)
    (slots : FrameSlots exec raw f)
    (values : f.vals=front++[val_ref (decodeRef type exec.slots.val[raw.base.val+dst.val]!)])
    (position : dst.val=Code.slots (f.locals.map Code.valueType)+Code.slots (front.map Code.valueType)) :
    runtime.interp.execute_ref_is_null exec raw.base dst dst ⦃ out =>
      out.1=.Ok () ∧ ∃ word : U64,
        word.val=Spec.referenceIsNull (decodeRef type exec.slots.val[raw.base.val+dst.val]!) ∧
        SlotsEffect exec out.2 (exec.slots.val.set (raw.base.val+dst.val) word) ∧
        FrameSlots out.2 raw {f with code:=after,vals:=front++[Abs.integerVal .I32 word.val]} ∧
        Abs.Stateful.Transition state f rest after .refIsNull
          (Abs.advance state {f with code:=after,vals:=front++[Abs.integerVal .I32 word.val]} rest) ⦄ := by
  have encoded := encode_decoded_ref type exec.slots.val[raw.base.val+dst.val]!
  have bound := (frame_read_word slots values position encoded).1
  apply WP.spec_mono (stateful_ref_is_null_effect exec raw.base dst dst type state f rest after front values bound bound)
  intro out effect
  obtain ⟨success,word,wordEq,written,transition⟩ := effect
  exact ⟨success,word,wordEq,written,frame_write_result slots values position bound written rfl,transition⟩
end Itasca.Runtime.Interp.Stateful
