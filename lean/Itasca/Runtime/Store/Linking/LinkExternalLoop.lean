import Itasca.Runtime.Store.Linking.ExternalMaps

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std
open Itasca.ModuleEnv

/-- The actual complete import loop preserves the store, terminates normally,
and constructs the typed per-index-space maps on successful linking. -/
theorem link_external_maps_loop {M : Type} (memory : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (laws : Platform.MemoryLaws memory view)
    (store : runtime.store.Store M) (shape : Shape view store)
    (module : runtime.compiler.ExecutableModule) (imports : Slice runtime.Extern)
    (lengths : imports.length = module.module.env.imports.length)
    (handles : ∀ external ∈ imports.val, ExternalIssued store external)
    {tables memories} (cache : Cache module.module.env tables memories)
    (inst : runtime.store.ModuleInst) (start : Usize) (startBound : start.val ≤ imports.length)
    (maps : LinkedMaps view store module (module.module.env.imports.val.take start.val) inst)
    (externals : ExternalMaps (imports.val.take start.val) inst) :
    runtime.store.instantiate.Store.prepare_instance_loop2 memory store imports (.Ok ()) start inst
      ⦃ out => out.1 = store ∧ out.2.2.module = module ∧
        (out.2.1 = .Ok () → LinkedMaps view store module module.module.env.imports.val out.2.2 ∧
          ExternalMaps imports.val out.2.2) ⦄ := by
  have hostSize : imports.length = imports.val.length := rfl
  have sourceSize : module.module.env.imports.length = module.module.env.imports.val.length := rfl
  unfold runtime.store.instantiate.Store.prepare_instance_loop2
  apply loop.spec_decr_nat (fun state => imports.length - state.2.2.1.val)
    (fun state => state.1 = store ∧ state.2.2.2.module = module ∧ state.2.2.1.val ≤ imports.length ∧
      (state.2.1 = .Ok () → LinkedMaps view store module
        (module.module.env.imports.val.take state.2.2.1.val) state.2.2.2 ∧
        ExternalMaps (imports.val.take state.2.2.1.val) state.2.2.2))
  · rintro ⟨current, status, index, currentInst⟩ ⟨sameStore, source, indexBound, mapping⟩
    dsimp only at sameStore source indexBound mapping ⊢
    subst current
    unfold runtime.store.instantiate.Store.prepare_instance_loop2.body
    dsimp only
    split
    · rename_i more
      have within : index.val < imports.length := by simpa using more
      cases status with
      | Err error => simp [core.result.Result.is_ok, source]
      | Ok value =>
        cases value
        obtain ⟨currentMaps, currentExternals⟩ := mapping rfl
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
        step with link_import_effect memory view laws store shape currentInst index external importBound typed issued room
          as ⟨status, after, nextInst, unchanged, effect⟩
        subst after
        step as ⟨next, increment⟩
        have nextSource : nextInst.module = module := by
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · exact source
          · exact linked.source.trans source
        refine ⟨nextSource, ?_, ?_, ?_⟩
        · omega
        · intro success
          rcases effect with ⟨error, status, rfl⟩ | ⟨ok, linked⟩
          · simp [status] at success
          · have extended := linked.maps currentMaps
            have externalExtended := linked.external_maps currentExternals
            have eq : currentInst.module.module.env.imports.val[index.val] =
                module.module.env.imports.val[index.val] := by simp only [source]
            constructor
            · rw [increment, List.take_succ_eq_append_getElem sourceBound]
              simpa only [eq] using extended
            · rw [increment, List.take_succ_eq_append_getElem within]
              simpa only [externalRead] using externalExtended
        · omega
    · rename_i stopped
      have atEnd : index.val = imports.length := by simp at stopped; omega
      simp only [WP.spec_ok]
      refine ⟨True.intro, source, ?_⟩
      intro success
      have finalMaps := mapping success
      constructor
      · simpa only [atEnd, lengths, List.take_length] using finalMaps.1
      · simpa only [atEnd, hostSize, List.take_length] using finalMaps.2
  · exact ⟨rfl, maps.source, startBound, fun _ => ⟨maps, externals⟩⟩


end Itasca.Runtime.Store
