import Itasca.Runtime.Interp.Relations.Defaults
import Itasca.Runtime.Representation.StoreCapacity
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Spec.FloatTrunc
import Itasca.Runtime.Interp.Relations.ReferenceSource
import Itasca.Runtime.Interp.Relations.StackPreservation
import Itasca.Runtime.SourceMachine.Core.Trap
import Itasca.Runtime.Interp.Relations.FrameStoreMetadata
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Interp.Control.StructuredLinear
import Itasca.Runtime.SourceMachine.Measure
import Itasca.Runtime.SourceMachine.Numeric.Decode
import Itasca.Runtime.Compiler.Local.Relations.Global.GlobalLowering

/-!
Sections, each formerly its own module: Globals, GlobalCoreWrite, GlobalMutation, GlobalCoreEmission, GlobalCoreOperands, GlobalCoreStep.
-/

/-! ## Globals -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

/-- Scalar global reads copy the exact stored low word and preserve the store
and all non-slot execution state. -/
theorem global_get_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val < exec.slots.length) :
    runtime.interp.execute_global_get memory exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        (exec.slots.val.set (base.val + dst.val) value.lo) ∧ out.2.2 = store ⦄ := by
  unfold runtime.interp.execute_global_get
  rw [vec_index_eq store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [vec_index_eq inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [vec_index_eq store.globals address.index value issued, bind_ok]
  step* <;> simp_all [SlotsEffect]

/-- Vector global reads copy both stored words in little-word order. -/
theorem global_get2_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (dst global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + dst.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_global_get2 memory exec store instanceIndex base dst global
      ⦃ out => out.1 = .Ok () ∧ SlotsEffect exec out.2.1
        ((exec.slots.val.set (base.val + dst.val) value.lo).set (base.val + dst.val + 1) value.hi) ∧
        out.2.2 = store ⦄ := by
  change base.val + dst.val + 2 ≤ exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_get2
  rw [vec_index_eq store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [vec_index_eq inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [vec_index_eq store.globals address.index value issued, bind_ok]
  step* <;> simp_all [SlotsEffect] <;> omega

/-- Scalar global writes change only the selected global's low word. The
stored type, high word and every other object are preserved exactly. -/
theorem global_set_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val < exec.slots.length) :
    runtime.interp.execute_global_set memory exec store instanceIndex base src global
      ⦃ out => out = (.Ok (), exec, {store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!})}) ⦄ := by
  change base.val + src.val < exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_set
  rw [vec_index_eq store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [vec_index_eq inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [vec_index_mut_eq store.globals address.index value issued, bind_ok]
  have lowFound : exec.slots.val[base.val + src.val]? = some exec.slots.val[base.val + src.val]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position, hposition⟩
  have positionEq : position.val = base.val + src.val := by simpa using hposition
  step with vec_index_given exec.slots position (exec.slots.val[base.val + src.val]!)
    (by simpa only [positionEq] using lowFound)
    as ⟨low, hlow⟩
  simp [hlow]


/-- Vector global writes retain exactly the two source words and preserve all
other global metadata and execution state. -/
theorem global_set2_dispatch_effect (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (src global : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.GlobalAddr) (value : runtime.store.GlobalInst)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.globals.val[global.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some value)
    (capacity : base.val + src.val + 2 ≤ exec.slots.length) :
    runtime.interp.execute_global_set2 memory exec store instanceIndex base src global
      ⦃ out => out = (.Ok (), exec, {store with globals := store.globals.set address.index ({value with lo := exec.slots.val[base.val + src.val]!, hi := exec.slots.val[base.val + src.val + 1]!})}) ⦄ := by
  change base.val + src.val + 2 ≤ exec.slots.val.length at capacity
  unfold runtime.interp.execute_global_set2
  rw [vec_index_eq store.instances instanceIndex inst found, bind_ok]
  simp only [lift, bind_ok]
  rw [vec_index_eq inst.globals (UScalar.cast .Usize global) address
    (by simpa only [U32.cast_Usize_val_eq] using mapped), bind_ok]
  rw [vec_index_mut_eq store.globals address.index value issued, bind_ok]
  have lowFound : exec.slots.val[base.val + src.val]? = some exec.slots.val[base.val + src.val]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position, hposition⟩
  have positionEq : position.val = base.val + src.val := by simpa using hposition
  step with vec_index_given exec.slots position (exec.slots.val[base.val + src.val]!)
    (by simpa only [positionEq] using lowFound)
    as ⟨low, hlow⟩
  have highFound : exec.slots.val[base.val + src.val + 1]? = some exec.slots.val[base.val + src.val + 1]! := by
    rw [getElem!_pos exec.slots.val _ (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  step as ⟨position2, hposition2⟩
  step as ⟨position3, hposition3⟩
  have positionEq2 : position3.val = base.val + src.val + 1 := by scalar_tac
  step with vec_index_given exec.slots position3 (exec.slots.val[base.val + src.val + 1]!)
    (by simpa only [positionEq2] using highFound)
    as ⟨high, hhigh⟩
  simp [hlow, hhigh]

end Itasca.Runtime.Interp

end

/-! ## GlobalCoreWrite -/

section

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

end

/-! ## GlobalMutation -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

/-- An instruction writes the represented source value into one existing global;
scalar writes retain the unused high word. -/
def GlobalMutation {M : Type} (before after : runtime.store.Store M) (value : val) : Prop :=
  ∃ index : Usize, ∃ old : runtime.store.GlobalInst, ∃ lo hi : U64,
    before.globals.val[index.val]? = some old ∧ old.ty.mutability = .Var ∧
    sourceType old.ty.valtype = Compiler.valueType value ∧
    pairWords old.ty.valtype (lo,hi) = Compiler.encodeValue value ∧
    (old.ty.valtype ≠ .V128 → hi = old.hi) ∧
    after = {before with globals := before.globals.set index {old with lo,hi}}

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_set_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : SourceMachine.AFrame) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (scalar : object.ty.valtype ≠ .V128) (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.execute_global_set memory exec store raw.instance raw.base src index
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
  have operand := (global_top_words exec raw f front value src values slots position).2
  have width : (Compiler.encodeValue value).length = 1 := by
    rw [Compiler.encode_value_length,←typed]
    cases eq : object.ty.valtype <;> simp only [sourceType,Compiler.width]
    exact False.elim (scalar eq)
  have capacity : raw.base.val+src.val < exec.slots.length := by
    have atZero := (operand 0 (by rw [width]; omega)).1
    simpa only [Nat.add_zero] using atZero
  have represented := operand.read_pair object.ty.valtype (by rw [Compiler.encode_value_length,←typed])
  have scalarType : sourceType object.ty.valtype ≠ .V128 := by
    cases eq : object.ty.valtype <;> simp only [sourceType,ne_eq,reduceCtorEq,not_false_eq_true]
    exact False.elim (scalar eq)
  simp only [pairWords,readPair,scalarType,ite_false] at represented
  apply WP.spec_mono (global_set_dispatch_effect memory exec store raw.instance raw.base src index inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨address.index,object,_,object.hi,issued,mutable,typed,?_,fun _ => rfl,rfl⟩
  simpa only [pairWords,scalarType,ite_false] using represented

theorem global_set2_mutation
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (f : SourceMachine.AFrame) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (vector : object.ty.valtype = .V128) (mutable : object.ty.mutability = .Var)
    (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      ⦃ out => GlobalMutation store out.2.2 value ⦄ := by
  have operand := (global_top_words exec raw f front value src values slots position).2
  have width : (Compiler.encodeValue value).length = 2 := by
    rw [Compiler.encode_value_length,←typed,vector]; rfl
  have capacity : raw.base.val+src.val+2 ≤ exec.slots.length := by
    have atOne := (operand 1 (by rw [width]; omega)).1
    change raw.base.val+src.val+1 < exec.slots.val.length at atOne
    change raw.base.val+src.val+2 ≤ exec.slots.val.length
    omega
  have represented := operand.read_pair object.ty.valtype (by rw [Compiler.encode_value_length,←typed])
  simp only [pairWords,readPair,vector,sourceType,ite_true] at represented
  apply WP.spec_mono (global_set2_dispatch_effect memory exec store raw.instance raw.base src index inst address object found mapped issued capacity)
  intro out effect
  subst out
  refine ⟨address.index,object,_,_,issued,mutable,typed,?_,fun h => False.elim (h vector),rfl⟩
  simpa only [pairWords,vector,sourceType,ite_true] using represented
end Itasca.Runtime.Interp

end

/-! ## GlobalCoreEmission -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std

theorem linear_emission_not_global_get {locals before after emitted index}
    (emission : Compiler.LinearEmission locals before (.GLOBAL_GET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_GET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem linear_emission_not_global_set {locals before after emitted index}
    (emission : Compiler.LinearEmission locals before (.GLOBAL_SET index) emitted after) : False := by
  generalize equality : instr.GLOBAL_SET index = instruction at emission
  cases emission with
  | binary stack ty op a b left right => cases op <;> simp [Compiler.IntegerBinary.source] at equality
  | numeric stack op a b left right =>
    have decoded := congrArg SourceMachine.Numeric.decodeInstruction equality
    rw [SourceMachine.Numeric.decode_instruction_source] at decoded
    simp [SourceMachine.Numeric.decodeInstruction] at decoded
  | _ => cases equality

theorem scalar_emission_global_get_inv {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.GLOBAL_GET (.mk_uN index)) emitted after) :
    ∃ mutability ty idx dst, index = idx.val ∧
      C.GLOBALS[index]? = some (.mk_globaltype mutability ty) ∧
      emitted = [Compiler.globalGetInstruction (decide (Compiler.width ty = 2)) dst idx] ∧
      after = before ++ [ty] ∧ dst.val = Compiler.slots C.LOCALS + Compiler.slots before := by
  generalize equality : instr.GLOBAL_GET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linear_emission_not_global_get pure)
  | globalGet stack mutability ty idx dst lookup position =>
    cases equality
    exact ⟨mutability,ty,idx,dst,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality

theorem scalar_emission_global_set_inv {C before after emitted} (index : Nat)
    (emission : Compiler.ScalarEmission C before (.GLOBAL_SET (.mk_uN index)) emitted after) :
    ∃ front ty idx src, index = idx.val ∧ before = front ++ [ty] ∧
      C.GLOBALS[index]? = some (.mk_globaltype (some .MUT) ty) ∧
      emitted = [Compiler.globalSetInstruction (decide (Compiler.width ty = 2)) src idx] ∧
      after = front ∧ src.val = Compiler.slots C.LOCALS + Compiler.slots front := by
  generalize equality : instr.GLOBAL_SET (.mk_uN index) = instruction at emission
  cases emission with
  | linear pure => rw [←equality] at pure; exact False.elim (linear_emission_not_global_set pure)
  | globalSet stack ty idx src lookup position =>
    cases equality
    exact ⟨_,ty,idx,src,rfl,rfl,lookup,rfl,rfl,position⟩
  | float stack other => cases other <;> simp [SourceMachine.Float.Instruction.source,SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
  | _ => simp [SourceMachine.Memory.Load.source,SourceMachine.Memory.Store.source] at equality
end Itasca.Runtime.Interp

end

/-! ## GlobalCoreOperands -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem global_lookup_back {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : SourceMachine.AFrame) (index sourceAddress : Nat)
    (sourceObject : globalinst) (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : f.module.GLOBALS[index]? = some sourceAddress)
    (issued : (Store.decodeStore view code store).GLOBALS[sourceAddress]? = some sourceObject) :
    ∃ address object, inst.globals.val[index]? = some address ∧
      store.globals.val[address.index.val]? = some object ∧ Store.decodeGlobal object = sourceObject := by
  rw [moduleEq] at mapped
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at issued
  obtain ⟨object,rawIssued,objectEq⟩ := Option.map_eq_some_iff.mp issued
  exact ⟨address,object,rawMapped,by simpa only [addressEq] using rawIssued,objectEq⟩

theorem core_global_lookup {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : SourceMachine.AFrame)
    (C : context) (index : Nat) (mutability : «mut») (ty : valtype)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (bindings : SourceMachine.ModuleBindings (Store.decodeStore view code store) f.module C)
    (lookup : C.GLOBALS[index]? = some (.mk_globaltype mutability ty)) :
    ∃ address object, inst.globals.val[index]? = some address ∧
      store.globals.val[address.index.val]? = some object ∧
      Store.decodeMut object.ty.mutability = mutability ∧ sourceType object.ty.valtype = ty := by
  obtain ⟨sourceAddress,sourceObject,mapped,issued,typeEq⟩ := bindings.global_lookup lookup
  obtain ⟨address,object,rawMapped,rawIssued,objectEq⟩ := global_lookup_back view code store inst f index sourceAddress sourceObject moduleEq mapped issued
  rw [←objectEq] at typeEq
  cases typeEq
  exact ⟨address,object,rawMapped,rawIssued,rfl,rfl⟩

theorem global_set_typed_operand {s : store} (f : SourceMachine.AFrame) (after : List instr) (index : Nat)
    (typed : SourceMachine.FrameTyped s {f with code := .GLOBAL_SET (.mk_uN index) :: after} []) :
    ∃ front value, f.vals = front ++ [value] ∧ wf_val value ∧
      (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ := SourceMachine.frame_typed_operands_bounds typed
  cases operation
  cases operandTypes with
  | cons valueTyped tail =>
    cases tail
    exact ⟨front,_,split,Itasca.Runtime.Spec.val_ok_wf valueTyped,heights⟩

end Itasca.Runtime.Interp

end

/-! ## GlobalCoreStep -/

section

/-!
Global instruction dispatch through decoded values to a concrete step. Scalar and two-word global representations retain their separate width obligations.
-/

/-! ## Global Core Dispatch -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_global_get {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (dst index : U32)
    (handler : (if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
        else runtime.interp.execute_global_get memory exec store inst base dst index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Compiler.globalGetInstruction wide dst index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Compiler.globalGetInstruction wide dst index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_get2 memory exec store inst base dst index
          else runtime.interp.execute_global_get memory exec store inst base dst index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩

theorem dispatch_global_set {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (frameIndex inst function base : Usize) (wide : Bool) (src index : U32)
    (handler : (if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
        else runtime.interp.execute_global_set memory exec store inst base src index) ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Compiler.globalSetInstruction wide src index) ⦃ out => Q (out.1,out.2.1,out.2.2.1) ∧ out.2.2.2 = platform ⦄ := by
  have equation : runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex inst function base
      (Compiler.globalSetInstruction wide src index) = (do
        let (result,next,nextStore) ← if wide then runtime.interp.execute_global_set2 memory exec store inst base src index
          else runtime.interp.execute_global_set memory exec store inst base src index
        Result.ok (result,next,nextStore,platform)) := by cases wide <;> rfl
  rw [equation]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next,nextStore⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl⟩
end Itasca.Runtime.Interp

end

/-! ## Global Core Dispatch Values -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem source_type_width_two (ty : Itasca.wasm_types.ValueType) :
    Compiler.width (sourceType ty) = 2 ↔ ty = .V128 := by
  cases ty <;> simp [sourceType,Compiler.width]

theorem source_type_width_scalar (ty : Itasca.wasm_types.ValueType) (scalar : ty ≠ .V128) :
    Compiler.width (sourceType ty) = 1 := by
  cases ty <;> simp_all [sourceType,Compiler.width]

theorem dispatch_global_get_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType))
    (capacity : raw.base.val + dst.val + Compiler.width (sourceType object.ty.valtype) ≤ exec.slots.length)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.globalGetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) dst index) ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ out.2.2.1 = store ∧
      ∃ nextFrame, SourceMachine.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  classical
  have handler : (if decide (Compiler.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_get2 memory exec store raw.instance raw.base dst index
      else runtime.interp.execute_global_get memory exec store raw.instance raw.base dst index) ⦃ out => out.1 = .Ok () ∧ out.2.2 = store ∧ ∃ nextFrame, SourceMachine.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ∧ {out.2.1 with slots := exec.slots} = exec ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
    simp only [source_type_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_get2_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by simpa only [vector,sourceType,Compiler.width] using capacity) vector
    · simp only [vector,decide_false,ite_false]
      exact global_get_core memory view code exec store raw dst index inst address object s f rest after
        found mapped issued storeEq moduleEq slots position (by rw [source_type_width_scalar _ vector] at capacity; omega) vector small
  apply WP.spec_mono (dispatch_global_get memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Compiler.width (sourceType object.ty.valtype) = 2)) dst index handler)
  intro out effect
  exact ⟨effect.1.1,effect.2,effect.1.2⟩

theorem dispatch_global_set_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : SourceMachine.AState) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Compiler.valueType value) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
      (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index) ⦃ out =>
      out.2.2.2 = platform ∧ out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame, SourceMachine.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  classical
  have handler : (if decide (Compiler.width (sourceType object.ty.valtype) = 2) then
      runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index
      else runtime.interp.execute_global_set memory exec store raw.instance raw.base src index) ⦃ out => out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧ ∃ nextFrame, SourceMachine.Core.globalSet s f rest index.val after = .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧ FrameSlots out.2.1 raw nextFrame ⦄ := by
    simp only [source_type_width_two]
    by_cases vector : object.ty.valtype = .V128
    · simp only [vector,decide_true,ite_true]
      exact global_set2_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
    · simp only [vector,decide_false,ite_false]
      exact global_set_core memory view code exec store raw src index inst address object s f rest after front value
        found mapped issued storeEq moduleEq slots values position vector mutable valueWf typed
  apply WP.spec_mono (dispatch_global_set memory hooks floats allocator exec store platform frameIndex raw.instance raw.function raw.base
    (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index handler)
  intro out effect
  exact ⟨effect.2,effect.1⟩

end Itasca.Runtime.Interp

end

/-! ## Global Core Step -/

section

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt Itasca.Runtime.Spec
variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem step_global_get_simulation (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (dst index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f)
    (position : dst.val = Compiler.slots ((f.locals ++ f.vals).map Compiler.valueType))
    (capacity : raw.base.val + dst.val + Compiler.width (sourceType object.ty.valtype) ≤ exec.slots.length)
    (small : object.ty.valtype = .I32 ∨ object.ty.valtype = .F32 → object.lo.val < 2^32)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.globalGetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) dst index))
    (pcBound : raw.pc.val < U32.max)
    (sourceTyped : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩) :
    let s : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.2 = platform ∧ out.2.2.1 = store ∧
      ∃ nextFrame, SourceMachine.Core.globalGet s f rest index.val after = .next {s with frames := nextFrame :: rest} ∧
        SourceMachine.CoreTyped {s with frames := nextFrame :: rest} ∧
        StepH (SourceMachine.decode s) [] (SourceMachine.decode {s with frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ∧ ∃ pc : U32, pc.val = raw.pc.val+1 ∧ {out.2.1 with slots := exec.slots} = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} ∧ SlotPrefix raw.base.val exec.slots.val out.2.1.slots.val ⦄ := by
  dsimp only
  obtain ⟨next,abstract,fresh,source⟩ := SourceMachine.Core.global_get_progress (Store.decodeStore view code store) ambient f rest index.val after sourceTyped
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Compiler.globalGetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) dst index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  apply WP.spec_mono (dispatch_global_get_core memory hooks floats allocator view code
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw dst index inst address object
    ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_GET (.mk_uN index.val) :: after} :: rest,[]⟩ f rest after platform frameIndex
    found mapped issued rfl moduleEq slots position capacity small)
  intro out effect
  obtain ⟨success,platformSame,storeSame,nextFrame,actual,represented,unchanged,prefixEffect⟩ := effect
  rw [actual] at abstract
  cases abstract
  exact ⟨success,platformSame,storeSame,nextFrame,actual,fresh,source,represented,pc,pcNext,unchanged,prefixEffect⟩

theorem step_global_set_simulation (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (ambient : frame) (f : SourceMachine.AFrame)
    (rest : List SourceMachine.AFrame) (after : List instr) (front : List val) (value : val)
    (platform : P) (frameIndex : Usize)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Compiler.slots ((f.locals ++ front).map Compiler.valueType))
    (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Compiler.valueType value)
    (compiled : runtime.bytecode.CompiledFunction)
    (last : frameIndex.val+1 = exec.frames.length)
    (frameFound : exec.frames.val[frameIndex.val]? = some raw)
    (codeFound : inst.module.functions.val[raw.function.val]? = some compiled)
    (fetched : compiled.code.val[raw.pc.val]? = some (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index))
    (pcBound : raw.pc.val < U32.max)
    (sourceTyped : SourceMachine.CoreTyped ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩) :
    let s : SourceMachine.AState := ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩
    runtime.interp.step memory hooks floats allocator exec store platform ⦃ out =>
      out.2.2.2 = platform ∧ out.1 = .Ok () ∧ (∃ pc : U32, pc.val = raw.pc.val+1 ∧ out.2.1 = {exec with frames := exec.frames.set frameIndex {raw with pc := pc}}) ∧ FrameStoreMetadata store out.2.2.1 ∧
      ∃ nextFrame, SourceMachine.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2.1, frames := nextFrame :: rest} ∧
        SourceMachine.CoreTyped {s with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest} ∧
        Extend_store s.store (Store.decodeStore view code out.2.2.1) ∧
        StepH (SourceMachine.decode s) [] (SourceMachine.decode {s with store := Store.decodeStore view code out.2.2.1,frames := nextFrame :: rest}) ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  dsimp only
  obtain ⟨next,abstract,fresh,extension,source⟩ := SourceMachine.Core.global_set_progress (Store.decodeStore view code store) ambient f rest index.val after sourceTyped
  apply step_fetch memory hooks floats allocator exec store platform frameIndex raw inst compiled
    (Compiler.globalSetInstruction (decide (Compiler.width (sourceType object.ty.valtype) = 2)) src index) last frameFound found codeFound fetched pcBound
  intro pc pcNext
  apply WP.spec_mono (dispatch_global_set_core memory hooks floats allocator view code
    {exec with frames := exec.frames.set frameIndex {raw with pc := pc}} store raw src index inst address object
    ⟨Store.decodeStore view code store,ambient,{f with code := .GLOBAL_SET (.mk_uN index.val) :: after} :: rest,[]⟩ f rest after front value platform frameIndex
    found mapped issued rfl moduleEq slots values position mutable valueWf typed)
  intro out effect
  obtain ⟨platformSame,success,unchanged,metadata,nextFrame,actual,represented⟩ := effect
  rw [actual] at abstract
  cases abstract
  exact ⟨platformSame,success,⟨pc,pcNext,unchanged⟩,metadata,nextFrame,actual,fresh,extension,source,represented⟩

end Itasca.Runtime.Interp

end

end
