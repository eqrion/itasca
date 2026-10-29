import Itasca.Runtime.Interp.State.GlobalCoreEmission
import Itasca.Runtime.SourceMachine.Core.Globals

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
