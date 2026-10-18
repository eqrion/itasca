import Exec.Store.Linking.LinkLoop
import Exec.Store.Linking.LinkSourceComplete

namespace Exec.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

private theorem forall₂_index {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) {index : Nat} (left : index < xs.length) (right : index < ys.length) :
    R xs[index] ys[index] := by
  induction related generalizing index with
  | nil => simp at left
  | cons head tail ih =>
    cases index with
    | zero => exact head
    | succ index => exact ih (by simpa using left) (by simpa using right)

private theorem link_specs_and {T : Type} {call : Result T} {P Q : T → Prop}
    (first : call ⦃ P ⦄) (second : call ⦃ Q ⦄) : call ⦃ out => P out ∧ Q out ⦄ := by
  obtain ⟨out, returned, hp⟩ := WP.spec_imp_exists first
  rw [returned, WP.spec_ok] at second ⊢
  exact ⟨hp, second⟩

/-- Source-typed imports cannot produce a Link rejection anywhere in the
actual import loop. The loop returns normally, preserves the store, and retains
the complete typed index maps on success. -/
theorem link_imports_source_typed {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (code : CodeInterpretation) (requiredTypes : List Itasca.types.ExternType)
    (resolved : List.Forall₂ (Itasca.ModuleExternals.ImportResolves module.module.env)
      module.module.env.imports.val requiredTypes)
    (typedImports : List.Forall₂ (fun external required =>
      Externaddr_ok (decodeStore view code store) (decodeExternal external)
        (Itasca.ModuleExternals.externalType required)) imports.val requiredTypes)
    (lengths : imports.length = module.module.env.imports.length)
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    {tables memories} (cache : Cache module.module.env tables memories)
    (inst : runtime.store.Instance) (start : Usize) (startBound : start.val ≤ imports.length)
    (maps : LinkedMaps view store module (module.module.env.imports.val.take start.val) inst) :
    runtime.store.instantiate.Store.instantiate_inner_loop2 memory store imports (.Ok ()) start inst
      ⦃ out => out.1 = store ∧ out.2.2.module = module ∧
        (out.2.1 = .Ok () ∨ out.2.1 = .Err .WrongStore) ∧
        (out.2.1 = .Ok () → LinkedMaps view store module module.module.env.imports.val out.2.2) ⦄ := by
  have hostSize : imports.length = imports.val.length := rfl
  have sourceSize : module.module.env.imports.length = module.module.env.imports.val.length := rfl
  unfold runtime.store.instantiate.Store.instantiate_inner_loop2
  apply loop.spec_decr_nat (fun state => imports.length - state.2.2.1.val)
    (fun state => state.1 = store ∧ state.2.2.2.module = module ∧ state.2.2.1.val ≤ imports.length ∧
      (state.2.1 = .Ok () ∨ state.2.1 = .Err .WrongStore) ∧
      (state.2.1 = .Ok () → LinkedMaps view store module
        (module.module.env.imports.val.take state.2.2.1.val) state.2.2.2))
  · rintro ⟨current, status, index, currentInst⟩ ⟨sameStore, source, indexBound, allowed, mapping⟩
    dsimp only at sameStore source indexBound allowed mapping ⊢
    subst current
    unfold runtime.store.instantiate.Store.instantiate_inner_loop2.body
    dsimp only
    split
    · rename_i more
      have within : index.val < imports.length := by simpa using more
      cases status with
      | Err error =>
        have sameError : error = .WrongStore := by simpa using allowed
        simp [core.result.Result.is_ok, source, sameError]
      | Ok value =>
        cases value
        have currentMaps := mapping rfl
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step as ⟨external, externalRead⟩
        have sourceBound : index.val < module.module.env.imports.val.length := by omega
        have importBound : index.val < currentInst.module.module.env.imports.length := by rw [source]; omega
        have typed : ∀ idx, currentInst.module.module.env.imports.val[index.val].desc = .Func idx →
            idx.val < currentInst.module.module.env.types.length := by
          intro idx desc
          simp only [source] at desc ⊢
          apply cache.import_indices idx
          exact List.mem_filterMap.mpr ⟨module.module.env.imports.val[index.val],
            List.getElem_mem (by omega), by simp [desc]⟩
        have issued : ExternalIssued store external := handles external (by rw [externalRead]; exact List.getElem_mem within)
        have mapLengths := currentMaps.lengths
        have prefixLen : (module.module.env.imports.val.take index.val).length = index.val := by simp; omega
        rw [prefixLen] at mapLengths
        have hostMax := imports.property
        have room : match currentInst.module.module.env.imports.val[index.val].desc with
            | .Func _ => currentInst.funcs.length < Usize.max
            | .Table _ => currentInst.tables.length < Usize.max
            | .Memory _ => currentInst.memories.length < Usize.max
            | .Global _ => currentInst.globals.length < Usize.max := by
          split <;> omega
        have requiredBound : index.val < requiredTypes.length := by
          rw [← resolved.length_eq]
          exact sourceBound
        have sourceResolved := forall₂_index resolved sourceBound requiredBound
        have sourceTyped := forall₂_index typedImports within requiredBound
        rw [← externalRead] at sourceTyped
        have accepted := link_import_source_typed memory view laws code store shape currentInst index external
          importBound requiredTypes[index.val] (by simpa only [source] using sourceResolved)
          issued sourceTyped room
        have structural := link_import_effect memory view laws store shape currentInst index external importBound typed issued room
        step with link_specs_and structural accepted
          as ⟨status, after, nextInst, unchanged, effect, unchangedAgain, statusAllowed⟩
        try subst after
        step as ⟨next, increment⟩
        have nextSource : nextInst.module = module := by
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · exact source
          · exact linked.source.trans source
        refine ⟨nextSource, ?_, statusAllowed, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · simp [status] at success
          · have extended := linked.maps currentMaps
            have eq : currentInst.module.module.env.imports.val[index.val] =
                module.module.env.imports.val[index.val] := by simp only [source]
            rw [increment, List.take_succ_eq_append_getElem sourceBound]
            simpa only [eq] using extended
        · omega
    · rename_i stopped
      have atEnd : index.val = imports.length := by simp at stopped; omega
      simp only [WP.spec_ok]
      refine ⟨True.intro, source, allowed, ?_⟩
      intro success
      have finalMaps := mapping success
      simpa only [atEnd, lengths, List.take_length] using finalMaps
  · exact ⟨rfl, maps.source, startBound, Or.inl rfl, fun _ => maps⟩

end Exec.Store
