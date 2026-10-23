import Exec.Interp.State.TableMutation
import Exec.Spec.TableWriteBounds
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

/-- The exact extracted table write implements the generated successful update
or bounds trap, and retains the current frame metadata in both cases. -/
theorem table_set_source_effect {M : Type}
    (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (exec : runtime.interp.Execution) (store : runtime.store.Store M)
    (instanceIndex base : Usize) (index value table : U32) (inst : runtime.store.ModuleInst)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (position : U32) (ambient : frame)
    (found : store.instances.val[instanceIndex.val]? = some inst)
    (mapped : inst.tables.val[table.val]? = some address)
    (issued : store.tables.val[address.index.val]? = some object)
    (input : UScalar.cast .U32 exec.slots.val[base.val+index.val]! = position)
    (indexBound : base.val+index.val < exec.slots.length)
    (valueBound : base.val+value.val < exec.slots.length)
    (moduleEq : ambient.MODULE = decodeInstance store inst)
    (storeWf : wf_store (decodeStore view code store)) (ambientWf : wf_frame ambient) :
    runtime.interp.execute_table_set memory exec store instanceIndex base index value table ⦃ out =>
      out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .TableOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 position.val,admininstr_ref (decodeRef object.ty exec.slots.val[base.val+value.val]!),.TABLE_SET (.mk_uN table.val)]⟩ []
        ⟨⟨decodeStore view code out.2.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .TableOutOfBounds) → out.2.2 = store) ⦄ := by
  apply WP.spec_mono (table_set_effect memory exec store instanceIndex base index value table
    inst address object position found mapped issued input indexBound valueBound)
  intro out effect
  split at effect
  · rename_i inside
    rw [effect]
    refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,Or.inl rfl,?_,by simp⟩
    exact table_write_source view code store inst ambient table position address object _ moduleEq mapped issued storeWf ambientWf inside
  · rename_i outside
    rw [effect]
    refine ⟨rfl,⟨rfl,rfl,rfl,rfl⟩,Or.inr rfl,?_,fun _ => rfl⟩
    apply Spec.table_set_trap_step _ _ _ _ _ storeWf ambientWf (by scalar_tac) (by scalar_tac)
    rw [table_lookup_decodes view code store inst ambient table address object moduleEq mapped issued]
    simpa [decodeTable] using Nat.le_of_not_gt outside
end Exec.Interp
