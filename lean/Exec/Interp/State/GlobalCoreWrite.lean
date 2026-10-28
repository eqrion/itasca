import Exec.Interp.State.GlobalCoreRead
import Exec.Interp.Relations.WordDecoding
import Exec.Interp.Relations.FrameStoreMetadata

namespace Itasca.Runtime.Interp
open Aeneas Aeneas.Std SpecExt

theorem core_global_set_value {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame) (rest : List Abs.AFrame)
    (after : List instr) (index : U32) (front : List val) (value : val)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (values : f.vals = front ++ [value]) (mutable : object.ty.mutability = .Var)
    (typed : Abs.valueType value = sourceType object.ty.valtype) :
    Abs.Core.globalSet s f rest index.val after =
      .next {s with store := Spec.globalWrite s.store f.toFrame index.val value, frames := {f with code := after, vals := front} :: rest} := by
  simp only [Abs.Core.globalSet,values,Abs.pop_append,moduleEq,Store.decodeInstance,List.getElem?_map,mapped,Option.map_some,
    storeEq,Store.decodeStore,issued,Store.decodeGlobal,mutable,Store.decodeMut,typed,ite_true,Abs.advance]

theorem global_top_words (exec : runtime.interp.Execution) (raw : runtime.interp.Frame)
    (f : Abs.AFrame) (front : List val) (value : val) (src : U32)
    (values : f.vals = front ++ [value]) (slots : FrameSlots exec raw f)
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType)) :
    ValuesAt exec.slots.val raw.base.val (f.locals ++ front) ∧
      WordsAt exec.slots.val (raw.base.val+src.val) (Code.encodeValue value) := by
  have all : WordsAt exec.slots.val raw.base.val
      (Code.encodeValues (f.locals ++ front) ++ Code.encodeValue value) := by
    have shape : f.locals ++ f.vals = (f.locals ++ front) ++ [value] := by simp [values,List.append_assoc]
    change ValuesAt exec.slots.val raw.base.val (f.locals ++ f.vals) at slots
    rw [shape] at slots
    change WordsAt _ _ (Code.encodeValues ((f.locals ++ front) ++ [value])) at slots
    rw [Code.encodeValues_append] at slots
    simpa only [Code.encodeValues,List.flatMap_cons,List.flatMap_nil,List.append_nil] using slots
  exact ⟨all.append_left,by simpa only [Code.encodeValues_length,position] using all.append_right⟩

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem global_set_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (scalar : object.ty.valtype ≠ .V128) (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.execute_global_set memory exec store raw.instance raw.base src index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      ∃ nextFrame, Abs.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  obtain ⟨prefixWords,operand⟩ := global_top_words exec raw f front value src values slots position
  have width : (Code.encodeValue value).length = 1 := by
    rw [Code.encodeValue_length,←typed]
    cases eq : object.ty.valtype <;> simp only [sourceType,Code.width]
    exact False.elim (scalar eq)
  have capacity : raw.base.val+src.val < exec.slots.length := by
    have atZero := (operand 0 (by rw [width]; omega)).1
    simpa only [Nat.add_zero] using atZero
  have numericType : Abs.valueType value = sourceType object.ty.valtype := by
    rw [←valueType_eq_abs]
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
  change Abs.Core.globalSet s f rest index.val after = _
  simpa only [storeEq,source] using abstract

theorem global_set2_core (view : M → Slice U8) (code : Store.CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (raw : runtime.interp.Frame)
    (src index : U32) (inst : runtime.store.ModuleInst) (address : runtime.GlobalAddr)
    (object : runtime.store.GlobalInst) (s : Abs.AState) (f : Abs.AFrame)
    (rest : List Abs.AFrame) (after : List instr) (front : List val) (value : val)
    (found : store.instances.val[raw.instance.val]? = some inst)
    (mapped : inst.globals.val[index.val]? = some address)
    (issued : store.globals.val[address.index.val]? = some object)
    (storeEq : s.store = Store.decodeStore view code store)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (slots : FrameSlots exec raw f) (values : f.vals = front ++ [value])
    (position : src.val = Code.slots ((f.locals ++ front).map Code.valueType))
    (vector : object.ty.valtype = .V128) (mutable : object.ty.mutability = .Var)
    (valueWf : wf_val value) (typed : sourceType object.ty.valtype = Code.valueType value) :
    runtime.interp.execute_global_set2 memory exec store raw.instance raw.base src index ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      ∃ nextFrame, Abs.Core.globalSet s f rest index.val after =
          .next {s with store := Store.decodeStore view code out.2.2, frames := nextFrame :: rest} ∧
        FrameSlots out.2.1 raw nextFrame ⦄ := by
  obtain ⟨prefixWords,operand⟩ := global_top_words exec raw f front value src values slots position
  have width : (Code.encodeValue value).length = 2 := by
    rw [Code.encodeValue_length,←typed,vector]
    rfl
  have capacity : raw.base.val+src.val+2 ≤ exec.slots.length := by
    have atOne := (operand 1 (by rw [width]; omega)).1
    change raw.base.val+src.val+1 < exec.slots.val.length at atOne
    change raw.base.val+src.val+2 ≤ exec.slots.val.length
    omega
  have numericType : Abs.valueType value = sourceType object.ty.valtype := by
    rw [←valueType_eq_abs]
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
  change Abs.Core.globalSet s f rest index.val after = _
  simpa only [storeEq,source] using abstract

end Itasca.Runtime.Interp
