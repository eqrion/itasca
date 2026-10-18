import Exec.Store.Api.ExportBounds
import Exec.Store.Linking.LinkEffects
namespace Exec.Store
open Aeneas Aeneas.Std

private theorem same_bytes_loop_total (left right : Slice U8) (index : Usize) (same : Bool)
    (lengths : left.length = right.length) (bound : index.val ≤ left.length) :
    runtime.store.same_bytes_loop left right index same ⦃ _ => True ⦄ := by
  unfold runtime.store.same_bytes_loop
  apply loop.spec_decr_nat (fun p => left.length - p.1.val) (fun p => p.1.val ≤ left.length)
  · rintro ⟨position,current⟩ bounded
    unfold runtime.store.same_bytes_loop.body
    dsimp only at bounded ⊢
    split
    · split
      · step
        step
        step as ⟨next,hnext⟩
        constructor <;> scalar_tac
      · simp
    · simp
  · exact bound

/-- The concrete byte-name comparison terminates for arbitrary slices. -/
theorem same_bytes_total (left right : Slice U8) :
    runtime.store.same_bytes left right ⦃ _ => True ⦄ := by
  unfold runtime.store.same_bytes
  dsimp only
  split
  · simp
  · apply same_bytes_loop_total
    · scalar_tac
    · simp

/-- Export scanning terminates and only returns handles from the completed
instance maps. Name comparison cannot authorize an unchecked descriptor. -/
theorem export_loop_issued {M : Type} (store : runtime.store.Store M)
    (inst : runtime.store.Instance) (shape : InstanceShape store inst)
    (bounds : ModuleExportBounds inst.module.module.env) (query : Slice U8)
    (index : Usize) (found : Option runtime.Extern)
    (position : index.val ≤ inst.module.module.env.exports.length)
    (prior : ∀ external ∈ found, ExternalIssued store external) :
    runtime.store.Store.export_loop query inst.funcs inst.tables inst.memories inst.globals
      inst.module.module.env index found ⦃ result => ∀ external ∈ result, ExternalIssued store external ⦄ := by
  unfold runtime.store.Store.export_loop
  apply loop.spec_decr_nat (fun p => inst.module.module.env.exports.length - p.1.val)
    (fun p => p.1.val ≤ inst.module.module.env.exports.length ∧ ∀ external ∈ p.2, ExternalIssued store external)
  · rintro ⟨offset,current⟩ ⟨position,issued⟩
    unfold runtime.store.Store.export_loop.body
    dsimp only at position issued ⊢
    simp only [module.Env.exports,Itasca.module.Env.impl.exports,alloc.vec.Vec.deref,bind_ok]
    split
    · have inBounds : offset.val < inst.module.module.env.exports.length := by
        have h := ‹offset < _›
        change offset.val < _ at h
        rw [Slice.len_val] at h
        simpa only [Slice.length,Slice.from_val] using h
      cases current with
      | some existing => simpa only [core.option.Option.is_none,Option.isNone,Bool.false_eq_true,↓reduceIte,WP.spec_ok] using issued
      | none =>
        simp only [core.option.Option.is_none,Option.isNone,↓reduceIte]
        step as ⟨entry,entryEq⟩
        have member : entry ∈ inst.module.module.env.exports.val := by simp [entryEq]
        have mapped := export_address_bounds bounds shape entry member
        have compared := same_bytes_total (alloc.vec.Vec.deref entry.name) query
        simp only [alloc.vec.Vec.deref] at compared
        step with compared as ⟨equal⟩
        cases equal with
        | false =>
          simp only [Bool.false_eq_true,↓reduceIte,bind_ok]
          step as ⟨next,nextEq⟩
          refine ⟨?_,by simp,?_⟩ <;> scalar_tac
        | true =>
          simp only [↓reduceIte]
          obtain ⟨_,_,_,_,_,_,_,_,functions,tables,memories,globals,_⟩ := shape
          cases descriptor : entry.desc <;> simp only [descriptor] at mapped ⊢
          all_goals
            step as ⟨addressIndex,indexEq⟩
            step as ⟨address,addressEq⟩
            step as ⟨next,nextEq⟩
            refine ⟨by scalar_tac,?_,by scalar_tac⟩
            intro external present
            have same := Option.mem_some_iff.mp present
            subst external
          · exact fun _ => (functions address (by simp [addressEq])).2
          · exact fun _ => (tables address (by simp [addressEq])).2
          · exact fun _ => (memories address (by simp [addressEq])).2
          · exact fun _ => (globals address (by simp [addressEq])).2
    · simpa only [WP.spec_ok] using issued
  · exact ⟨position,prior⟩

/-- Every issued instance handle has a total export lookup. Foreign handles
return WrongStore; every returned external handle remains issued. -/
theorem export_issued {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (store : runtime.store.Store M) (shape : Shape view store)
    (bounds : ExportBounds store) (address : runtime.InstanceAddr) (query : Slice U8)
    (issued : address.store = store.id → address.index.val < store.instances.length) :
    runtime.store.Store.export memory store address query ⦃ result =>
      (address.store ≠ store.id ∧ result = .Err .WrongStore) ∨
      (address.store = store.id ∧ ∃ found, result = .Ok found ∧
        ∀ external ∈ found, ExternalIssued store external) ⦄ := by
  by_cases owner : address.store = store.id
  · have bound := issued owner
    cases address with
    | mk id index =>
      dsimp only at owner bound
      subst id
      unfold runtime.store.Store.export
      simp only [runtime.store.Store.check,↓reduceIte,bind_ok,
        core.result.Result.Insts.CoreOpsTry.branch]
      step as ⟨inst,instEq⟩
      have found : store.instances.val[index.val]? = some inst := by simp [instEq]
      have instShape := shape.instances inst (List.mem_of_getElem? found)
      have instBounds := bounds index.val inst found
      simp only [runtime.compiler.ExecutableModule.env,module.Module.env,Itasca.module.Module.impl.env,bind_ok]
      step with export_loop_issued store inst instShape instBounds query 0#usize none (by simp) (by simp) as ⟨answer,output⟩
      exact Or.inr ⟨answer,rfl,output⟩
  · unfold runtime.store.Store.export
    simp [runtime.store.Store.check,owner,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
end Exec.Store
