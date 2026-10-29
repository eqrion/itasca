import Itasca.Runtime.Interp.Memory.MemoryCoreStore
import Itasca.Runtime.SourceMachine.Core.MemoryAccess

/-!
Scalar memory operand inversion and bounds. Typed operands supply the address/value facts needed to justify their concrete slot accesses.
-/

/-! ## Memory Core Operands -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt

 theorem memory_lookup_back {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : Abs.AFrame)
    (sourceAddress : Nat) (sourceObject : meminst)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (mapped : f.module.MEMS[0]? = some sourceAddress)
    (issued : (Store.decodeStore view code store).MEMS[sourceAddress]? = some sourceObject) :
    ∃ address object, inst.memories.val[0]? = some address ∧
      store.memories.val[address.index.val]? = some object := by
  rw [moduleEq] at mapped
  simp only [Store.decodeInstance,List.getElem?_map] at mapped
  obtain ⟨address,rawMapped,addressEq⟩ := Option.map_eq_some_iff.mp mapped
  simp only [Store.decodeStore,List.getElem?_map] at issued
  obtain ⟨object,rawIssued,objectEq⟩ := Option.map_eq_some_iff.mp issued
  exact ⟨address,object,rawMapped,by simpa only [addressEq] using rawIssued⟩

end Itasca.Runtime.Interp.MemoryDescriptor

end

/-! ## Memory Core Operand Bounds -/

section

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std SpecExt
 theorem load_typed_operands_full {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : Abs.AFrame)
    (after : List instr) (op : Abs.Memory.Load) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} []) :
    ∃ front bits address object, f.vals = front ++ [Abs.integerVal .I32 bits] ∧ bits < 2^32 ∧
      inst.memories.val[0]? = some address ∧ store.memories.val[address.index.val]? = some object ∧ Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    Abs.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup present
  obtain ⟨address,object,rawMapped,rawFound⟩ := memory_lookup_back view code store inst f sourceAddress sourceObject moduleEq mapped found
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail
    obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty := .I32) addressTyped
    exact ⟨front,bits,address,object,split,bitsBound,rawMapped,rawFound,frontWf,heights⟩

 theorem store_typed_operands_full {M : Type} (view : M → Slice U8) (code : Store.CodeInterpretation)
    (store : runtime.store.Store M) (inst : runtime.store.ModuleInst) (f : Abs.AFrame)
    (after : List instr) (op : Abs.Memory.Store) (argument : memarg)
    (moduleEq : f.module = Store.decodeInstance store inst)
    (typed : Abs.FrameTyped (Store.decodeStore view code store) {f with code := op.source argument :: after} []) :
    ∃ front bits number address object, f.vals = front ++ [Abs.integerVal .I32 bits,.CONST op.type number] ∧
      bits < 2^32 ∧ wf_num_ op.type number ∧ inst.memories.val[0]? = some address ∧
      store.memories.val[address.index.val]? = some object ∧ Forall wf_val front ∧ (∀ label ∈ f.labels, label.height ≤ front.length) := by
  obtain ⟨C,front,operands,ins,outs,bindings,_,operation,split,operandTypes,frontWf,heights⟩ :=
    Abs.frame_typed_operands_bounds typed
  obtain ⟨rfl,rfl,present⟩ := op.typing argument operation
  obtain ⟨sourceAddress,sourceObject,mapped,found⟩ := bindings.memory_lookup present
  obtain ⟨address,object,rawMapped,rawFound⟩ := memory_lookup_back view code store inst f sourceAddress sourceObject moduleEq mapped found
  cases operandTypes with
  | cons addressTyped tail =>
    cases tail with
    | cons valueTyped tail =>
      cases tail
      obtain ⟨bits,rfl,bitsBound⟩ := Abs.integer_val_inv (ty := .I32) addressTyped
      obtain ⟨number,rfl,numberWf⟩ := Abs.Core.numeric_value_inv valueTyped
      exact ⟨front,bits,number,address,object,split,bitsBound,numberWf,rawMapped,rawFound,frontWf,heights⟩
end Itasca.Runtime.Interp.MemoryDescriptor

end
