import Itasca.Runtime.Interp.Memory.MemoryCoreStore
import Itasca.Runtime.Abs.Core.MemoryLoad
import Itasca.Runtime.Abs.Core.MemoryStore
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
