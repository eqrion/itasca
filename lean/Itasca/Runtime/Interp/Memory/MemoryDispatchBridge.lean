import Itasca.Runtime.Interp.Memory.MemoryMutation
import Itasca.Runtime.Code.Local.Relations.Memory.MemoryOpcode

namespace Itasca.Runtime.Interp.MemoryDescriptor
open Aeneas Aeneas.Std

variable {M P F A : Type} (memory : runtime.platform.MemoryBuffer M)
  (hooks : runtime.platform.Platform P M) (floats : runtime.platform.FloatOps F)
  (allocator : runtime.platform.Alloc A)

theorem dispatch_load_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Memory.Load) (dst address offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryLoadInstruction op dst address offset) = (do
        let (result,next) ← runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset
        Result.ok (result,next,store,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Code.memoryLoadInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_load,runtime.interp.load_operands,loadOpcode,numericLoadOpcode,bind_ok]
  | packed ty width sign => cases ty <;> cases width <;> cases sign <;>
    simp [Code.memoryLoadInstruction,runtime.interp.dispatch,runtime.interp.dispatch_load,
      runtime.interp.load_operands,loadOpcode,packed,PackedMemory.loadOpcode,bind_ok]

theorem dispatch_store_eq (exec : runtime.interp.Execution)
    (store : runtime.store.Store M) (platform : P) (index inst function base : Usize)
    (op : Abs.Memory.Store) (address value offset : U32) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryStoreInstruction op address value offset) = (do
        let (result,next) ← runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset
        Result.ok (result,exec,next,platform)) := by
  cases op with
  | full ty => cases ty <;> simp [Code.memoryStoreInstruction,runtime.interp.dispatch,
      runtime.interp.dispatch_store,runtime.interp.store_operands,storeOpcode,numericStoreOpcode,bind_ok]
  | packed ty width => cases ty <;> cases width <;>
    simp [Code.memoryStoreInstruction,runtime.interp.dispatch,runtime.interp.dispatch_store,
      runtime.interp.store_operands,storeOpcode,packed,PackedMemory.storeOpcode,bind_ok]

theorem dispatch_load {Q : core.result.Result Unit runtime.ExecError × runtime.interp.Execution → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : Abs.Memory.Load) (dst address offset : U32)
    (handler : runtime.interp.execute_load memory exec store inst base (loadOpcode op) dst address offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryLoadInstruction op dst address offset) ⦃ out =>
        Q (out.1,out.2.1) ∧ out.2.2.1 = store ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_load_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩

theorem dispatch_store {Q : core.result.Result Unit runtime.ExecError × runtime.store.Store M → Prop}
    (exec : runtime.interp.Execution) (store : runtime.store.Store M) (platform : P)
    (index inst function base : Usize) (op : Abs.Memory.Store) (address value offset : U32)
    (handler : runtime.interp.execute_store memory exec store inst base (storeOpcode op) address value offset ⦃ Q ⦄) :
    runtime.interp.dispatch memory hooks floats allocator exec store platform index inst function base
      (Code.memoryStoreInstruction op address value offset) ⦃ out =>
        Q (out.1,out.2.2.1) ∧ out.2.1 = exec ∧ out.2.2.2 = platform ⦄ := by
  rw [dispatch_store_eq]
  obtain ⟨out,result,property⟩ := WP.spec_imp_exists handler
  rw [result]
  rcases out with ⟨r,next⟩
  simp only [bind_ok]
  with_unfolding_all apply WP.spec.ret
  exact ⟨property,rfl,rfl⟩
end Itasca.Runtime.Interp.MemoryDescriptor
