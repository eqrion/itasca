import Itasca.Runtime.Representation.Collection
import Itasca.Runtime.Interp.State.Globals
import Itasca.Runtime.Spec.Globals
import Itasca.Runtime.Interp.Relations.WordEncoding
import Itasca.Runtime.Interp.Relations.PrefixEffect
import Itasca.Runtime.SourceMachine.Core.Globals
import Itasca.Runtime.Interp.Relations.WordDecoding
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata

/-!
Core global reads and writes with decoded source correspondence. The shared value representation justifies both scalar and two-word accesses and the resulting source-store update.
-/

/-! ## Global Source -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt
open Itasca.Runtime.Store

/-- The two-word concrete replacement decodes to the generated global update.
The same identity covers scalar writes by retaining the original high word. -/
theorem global_write_decodes {M : Type} (view : M → Slice U8) (code : CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (ambient : frame)
    (index : U32) (address : runtime.GlobalAddr) (old : runtime.store.GlobalInst)
    (low high : U64) (moduleEq : ambient.MODULE = decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (found : store.globals.val[address.index.val]? = some old) :
    decodeStore view code {store with globals := store.globals.set address.index {old with lo := low, hi := high}} =
      Spec.globalWrite (decodeStore view code store) ambient index.val (decodeWords old.ty.valtype low high) := by
  have read : ambient.MODULE.GLOBALS[index.val]! = address.index.val := by
    rw [moduleEq]
    simp only [decodeInstance, List.getElem!_eq_getElem?_getD, List.getElem?_map, mapped, Option.map_some, Option.getD_some]
  have lists := Itasca.Runtime.Representation.map_set_modify decodeGlobal
    (fun global => {global with VALUE := decodeWords old.ty.valtype low high})
    store.globals.val address.index.val old {old with lo := low, hi := high} found rfl
  unfold Spec.globalWrite
  rw [read]
  unfold decodeStore
  simp only [alloc.vec.Vec.set_val_eq, lists]
  rfl

end Itasca.Runtime.Interp

end

/-! ## Global Core Read -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem core_global_get_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (index : U32)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object) :
    SourceMachine.Core.globalGet s f rest index.val after =
      .next {s with frames := {f with code := after, vals := f.vals ++ [Store.decodeWords object.ty.valtype object.lo object.hi]} :: rest} := by
  simp only [SourceMachine.Core.globalGet,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,Store.decodeGlobal,SourceMachine.advance]

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_get_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType))
    (capacity : raw.base.val + dst.val < exec.slots.length)
    (scalar : object.ty.valtype ≠ .V128)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32) :
    runtime.interp.execute_global_get memory exec store raw.instance raw.base dst index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ nextFrame, SourceMachine.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have abstract := core_global_get_value view code store inst address object s f rest after index storeEq moduleEq mapped issued
  have represented := ValuesAt.append_scalar slots object.ty.valtype object.lo object.hi scalar small
    (by simpa only [position] using capacity)
  apply WP.spec_mono (global_get_dispatch_effect memory exec store raw.instance raw.base dst index
    inst address object found mapped issued capacity)
  intro out effect
  refine ⟨effect.1,effect.2.2,_,abstract,?_,effect.2.1.2,?_⟩
  · change ValuesAt out.2.1.slots.val raw.base.val (f.locals ++ (f.vals ++ [_]))
    rw [effect.2.1.1,position]
    simpa only [List.append_assoc] using represented
  · rw [effect.2.1.1]
    exact SlotPrefix.set _ _ _ _ (by omega)

theorem global_get2_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType))
    (capacity : raw.base.val + dst.val + 2 ≤ exec.slots.length)
    (vector : object.ty.valtype = .V128) :
    runtime.interp.execute_global_get2 memory exec store raw.instance raw.base dst index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2 = store ∧
      ∃ nextFrame, SourceMachine.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  have abstract := core_global_get_value view code store inst address object s f rest after index storeEq moduleEq mapped issued
  have represented := ValuesAt.append_vector slots object.lo object.hi (by simpa only [position] using capacity)
  apply WP.spec_mono (global_get2_dispatch_effect memory exec store raw.instance raw.base dst index
    inst address object found mapped issued capacity)
  intro out effect
  refine ⟨effect.1,effect.2.2,_,abstract,?_,effect.2.1.2,?_⟩
  · change ValuesAt out.2.1.slots.val raw.base.val (f.locals ++ (f.vals ++ [_]))
    rw [effect.2.1.1,position,vector]
    simpa only [List.append_assoc] using represented
  · rw [effect.2.1.1]
    exact (SlotPrefix.set _ _ _ _ (by omega)).trans (SlotPrefix.set _ _ _ _ (by omega))

end Itasca.Runtime.Interp

end

/-! ## Global Core Write -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem core_global_set_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame) (rest : List SourceMachine.AFrame)
    (after : List instr) (index : U32) (front : List val) (value : val)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (values : f.vals = front ++ [value]) (mutable : object.ty.mutability = .Var)
    (typed : SourceMachine.valueType value = sourceType object.ty.valtype) :
    SourceMachine.Core.globalSet s f rest index.val after =
      .next {s with store := Spec.globalWrite s.store f.toFrame index.val value, frames := {f with code := after, vals := front} :: rest} := by
  simp only [SourceMachine.Core.globalSet,values,SourceMachine.pop_append,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,Store.decodeGlobal,mutable,Store.decodeMut,typed,ite_true,SourceMachine.advance]

theorem global_top_words (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (f : SourceMachine.AFrame) (front : List val) (value : val) (src : U32)
    (values : f.vals = front ++ [value]) (slots : FrameSlots exec raw f)
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType)) :
    ValuesAt exec.slots.val raw.base.val (f.locals ++ front) ∧
      WordsAt exec.slots.val (raw.base.val+src.val) (Compiler.encodeValue value) := by
  have all : WordsAt exec.slots.val raw.base.val
      (Compiler.encodeValues (f.locals ++ front) ++ Compiler.encodeValue value) := by
    have shape : f.locals ++ f.vals = (f.locals ++ front) ++ [value] := by simp [values,List.append_assoc]
    change ValuesAt exec.slots.val raw.base.val (f.locals ++ f.vals) at slots
    rw [shape] at slots
    change WordsAt _ _ (Compiler.encodeValues ((f.locals ++ front) ++ [value])) at slots
    rw [Compiler.encode_values_append] at slots
    simpa only [Compiler.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil] using slots
  exact ⟨all.append_left,by simpa only [Compiler.encode_values_length,position] using all.append_right⟩

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_set_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (scalar : object.ty.valtype ≠ .V128) (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.execute_global_set memory exec store raw.instance raw.base src index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      ∃ nextFrame, SourceMachine.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  obtain ⟨prefixWords,operand⟩ := global_top_words exec raw f front value src values slots position
  have width : (Compiler.encodeValue value).length = 1 := by
    rw [Compiler.encode_value_length,←typed]
    cases eq : object.ty.valtype <;> simp only [sourceType,Compiler.width]
    exact False.elim (scalar eq)
  have capacity : raw.base.val+src.val < exec.slots.length := by
    have atZero := (operand 0 (by rw [width]; omega)).1
    simpa only [Nat.add_zero] using atZero
  have numericType : SourceMachine.valueType value = sourceType object.ty.valtype := by
    rw [←value_type_eq_abs]
    exact typed.symm
  have abstract := core_global_set_value view code store inst address object s f rest after index front value
    storeEq moduleEq mapped issued values mutable numericType
  have decoded := operand.decode_value object.ty.valtype value valueWf typed
  have scalarType : sourceType object.ty.valtype ≠ .V128 := by
    cases eq : object.ty.valtype <;> simp only [sourceType,ne_eq,reduceCtorEq,not_false_eq_true]
    exact False.elim (scalar eq)
  simp only [readPair,scalarType,ite_false] at decoded
  have source := global_write_decodes view code store inst f.toFrame index address object
    exec.slots.val[raw.base.val+src.val]! object.hi moduleEq mapped issued
  rw [decode_words_scalar _ _ _ scalar,decoded] at source
  apply WP.spec_mono (global_set_dispatch_effect memory exec store raw.instance raw.base src index
    inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨rfl,rfl,⟨rfl,rfl,rfl,rfl⟩,{f with code := after, vals := front},?_,prefixWords⟩
  change SourceMachine.Core.globalSet s f rest index.val after = _
  simpa only [storeEq,source] using abstract

theorem global_set2_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (vector : object.ty.valtype = .V128) (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      ∃ nextFrame, SourceMachine.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  obtain ⟨prefixWords,operand⟩ := global_top_words exec raw f front value src values slots position
  have width : (Compiler.encodeValue value).length = 2 := by
    rw [Compiler.encode_value_length,←typed,vector]
    rfl
  have capacity : raw.base.val+src.val+2 ≤ exec.slots.length := by
    have atOne := (operand 1 (by rw [width]; omega)).1
    change raw.base.val+src.val+1 < exec.slots.val.length at atOne
    change raw.base.val+src.val+2 ≤ exec.slots.val.length
    omega
  have numericType : SourceMachine.valueType value = sourceType object.ty.valtype := by
    rw [←value_type_eq_abs]
    exact typed.symm
  have abstract := core_global_set_value view code store inst address object s f rest after index front value
    storeEq moduleEq mapped issued values mutable numericType
  have decoded := operand.decode_value object.ty.valtype value valueWf typed
  simp only [readPair,vector,sourceType,ite_true] at decoded
  have source := global_write_decodes view code store inst f.toFrame index address object
    exec.slots.val[raw.base.val+src.val]! exec.slots.val[raw.base.val+src.val+1]! moduleEq mapped issued
  rw [vector,decoded] at source
  apply WP.spec_mono (global_set2_dispatch_effect memory exec store raw.instance raw.base src index
    inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨rfl,rfl,⟨rfl,rfl,rfl,rfl⟩,{f with code := after, vals := front},?_,prefixWords⟩
  change SourceMachine.Core.globalSet s f rest index.val after = _
  simpa only [storeEq,source] using abstract

end Itasca.Runtime.Interp

end
