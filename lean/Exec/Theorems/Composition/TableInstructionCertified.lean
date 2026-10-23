import Exec.Interp.State.TableWriteSource
import Exec.Theorems.Composition.Certified.CertifiedContentUpdate
import Exec.Theorems.Composition.Certified.CertifiedCoreContent
import Exec.Store.Invariant.FunctionCapacities
import Exec.Store.Invariant.ObjectExtension
import Exec.Store.Invariant.SemanticApi
namespace Exec.Theorems
open Aeneas Aeneas.Std SpecExt Exec.Store Exec.Interp

theorem table_mutation_shape {M : Type} (view : M → Slice U8)
    (before after : runtime.store.Store M) (shape : Shape view before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) : Shape view after := by
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  have old := shape.tables object (List.mem_of_getElem? issued)
  apply shape.table_replace_same_length address.index bound {object with elements := words}
  · refine ⟨by simpa only [lengthEq] using old.1,by simpa only [lengthEq] using old.2.1,?_⟩
    intro word member
    rcases references word member with previous | changed
    · exact old.2.2 word previous
    · simpa only [changed] using reference
  · simpa only [found] using lengthEq

/-- Typed table content replacement retains decoded store extension. -/
theorem table_mutation_extends {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (shape : Shape view before) (syntaxProof : StoreSyntax code before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    Shape view after ∧ Extend_store (decodeStore view code before) (decodeStore view code after) := by
  have fresh := table_mutation_shape view before after shape address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  obtain ⟨bound,found⟩ := List.getElem?_eq_some_iff.mp issued
  let after := {before with tables := before.tables.set address.index {object with elements := words}}
  have sourceSyntax : StoreSyntax code after := syntaxProof
  have oldWf := decodeStore_wf view code before shape syntaxProof
  have newWf := decodeStore_wf view code after fresh sourceSyntax
  have oldTableWf : wf_tableinst (decodeTable object) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    exact decodeLimits_wf _ _ (shape.tables object (List.mem_of_getElem? issued)).1
  have newTableWf : wf_tableinst (decodeTable {object with elements := words}) := by
    apply wf_tableinst.tableinst_case_
    apply wf_tabletype.tabletype_case_0
    apply decodeLimits_wf
    simpa only [lengthEq] using (shape.tables object (List.mem_of_getElem? issued)).1
  have objectExtension := decodeTable_extends object {object with elements := words}
    rfl rfl (Nat.le_of_eq lengthEq.symm) oldTableWf newTableWf
  refine ⟨fresh,?_⟩
  unfold after at newWf
  rw [decodeStore_table_update view code before (before.tables.set address.index {object with elements := words})] at newWf ⊢
  simp only [alloc.vec.Vec.set_val_eq,List.map_set] at newWf ⊢
  apply Spec.extend_store_set_table _ _ _ oldWf
  · simpa only [decodeStore] using newWf
  · intro indexBound
    simpa only [decodeStore,found,
      getElem!_pos (before.tables.val.map decodeTable) address.index.val
        (by simpa only [List.length_map] using bound),List.getElem_map] using objectExtension

/-- The mutable Core certificate survives table-content replacement; the
new reference is required to be an issued value of the table's element type. -/
theorem table_mutation_core_certified {M : Type} (view : M → Slice U8)
    (code : CodeInterpretation) (before after : runtime.store.Store M)
    (certified : CertifiedCoreStore view code before)
    (address : runtime.TableAddr) (object : runtime.store.TableInst) (replacement : U64)
    (issued : before.tables.val[address.index.val]? = some object)
    (mutation : TableMutation before after address object replacement)
    (reference : ReferenceShape before object.ty replacement) :
    CertifiedCoreStore view code after ∧ Extend_store (decodeStore view code before) (decodeStore view code after) := by
  obtain ⟨shape,extension⟩ := table_mutation_extends view code before after certified.shape certified.storeSyntax
    address object replacement issued mutation reference
  obtain ⟨words,rfl,lengthEq,references⟩ := mutation
  exact ⟨certified.content_update rfl rfl rfl rfl rfl rfl shape extension,extension⟩
theorem table_set_core_certified {M : Type}
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
    (certified : CertifiedCoreStore view code store)
    (reference : ReferenceShape store object.ty exec.slots.val[base.val+value.val]!) (ambientWf : wf_frame ambient) :
    runtime.interp.execute_table_set memory exec store instanceIndex base index value table ⦃ out =>
      CertifiedCoreStore view code out.2.2 ∧
      Extend_store (decodeStore view code store) (decodeStore view code out.2.2) ∧
      out.2.1 = exec ∧ FrameStoreMetadata store out.2.2 ∧
      (out.1 = .Ok () ∨ out.1 = .Err (.Trap .TableOutOfBounds)) ∧
      StepH ⟨⟨decodeStore view code store,ambient⟩,
        [Spec.Segment.i32 position.val,admininstr_ref (decodeRef object.ty exec.slots.val[base.val+value.val]!),.TABLE_SET (.mk_uN table.val)]⟩ []
        ⟨⟨decodeStore view code out.2.2,ambient⟩,match out.1 with | .Ok _ => [] | .Err _ => [.TRAP]⟩ ∧
      (out.1 = .Err (.Trap .TableOutOfBounds) → out.2.2 = store) ⦄ := by
  have storeWf := decodeStore_wf view code store certified.shape certified.storeSyntax
  obtain ⟨out,run,source⟩ := WP.spec_imp_exists
    (table_set_source_effect memory view code exec store instanceIndex base index value table inst address object position ambient
      found mapped issued input indexBound valueBound moduleEq storeWf ambientWf)
  have changed := table_set_mutation memory exec store instanceIndex base index value table inst address object position
    found mapped issued input indexBound valueBound
  rw [run,WP.spec_ok] at changed ⊢
  rcases changed.2.2 with ⟨success,mutation⟩ | ⟨trap,unchanged⟩
  · obtain ⟨fresh,extension⟩ := table_mutation_core_certified view code store out.2.2 certified address object _ issued mutation reference
    exact ⟨fresh,extension,source⟩
  · exact ⟨by simpa only [unchanged] using certified,
      by simpa only [unchanged] using Spec.extend_store_refl _ storeWf,source⟩
end Exec.Theorems
