import Itasca.Runtime.Store.Invariant.TypeStaging
import Itasca.Runtime.Store.Invariant.FunctionTypeCauses
import Itasca.Runtime.Store.Preparation.PreparationCalls
namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

abbrev typeStageCall {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (state : runtime.store.Store M × runtime.store.ModuleInst) (index : Usize) :=
  runtime.store.instantiate.Store.add_instance_type memory allocator state.1 state.2 index

/-- A reached canonical-signature refusal, preceded only by actual successful
calls from the given type-loop input. -/
def TypeStagingCause {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (store : runtime.store.Store M) (inst : runtime.store.ModuleInst)
    (start : Usize) (error : runtime.ExecError) : Prop :=
  ∃ current currentInst index ty,
    PreparationCalls (typeStageCall memory allocator) (store,inst) start (current,currentInst) index ∧
    currentInst.module.module.env.types.val[index.val]? = some ty ∧
    runtime.store.instantiate.Store.add_instance_type memory allocator current currentInst index = .ok (.Err error,current,currentInst) ∧
    ty ∉ current.types.val ∧ TypeInternResourceCause allocator current ty error

/-- Type canonicalization is total and preserves all other prepared maps. Its
successful type vector resolves every source signature to an exact store entry. -/
theorem type_staging_resource_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (start : Usize) (startBound : start.val ≤ seed.module.module.env.types.val.length)
    (changed : store = {before with types := store.types, signature_values := store.signature_values})
    (instChanged : inst = {seed with types := inst.types})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (entries : TypeEntries store (seed.module.module.env.types.val.take start.val) inst.types.val) :
    runtime.store.instantiate.Store.prepare_instance_loop3 memory allocator store (.Ok ()) start inst
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with types := after.types, signature_values := after.signature_values} ∧
        next = {seed with types := next.types} ∧ StagedPrefix before after ∧
        objectCount after ≤ Usize.max ∧
        (status = .Ok () → TypeEntries after seed.module.module.env.types.val next.types.val) ∧
        (∀ error, status = .Err error → TypeStagingCause memory allocator store inst start error) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop3
  apply loop.spec_decr_nat (fun state => seed.module.module.env.types.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with types := state.1.types, signature_values := state.1.signature_values} ∧
      state.2.2.2 = {seed with types := state.2.2.2.types} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧ state.2.2.1.val ≤ seed.module.module.env.types.val.length ∧
      (state.2.1 = .Ok () → TypeEntries state.1 (seed.module.module.env.types.val.take state.2.2.1.val)
        state.2.2.2.types.val) ∧
      (state.2.1 = .Ok () → PreparationCalls (typeStageCall memory allocator) (store,inst) start (state.1,state.2.2.2) state.2.2.1) ∧
      (∀ error, state.2.1 = .Err error → TypeStagingCause memory allocator store inst start error))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, indexBound, typing, trace, cause⟩
    dsimp only at currentChanged mapChanged prefixStore bound indexBound typing ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop3.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.metadata.Module.impl.env, Itasca.metadata.Env.impl.types, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.types.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, by simp, cause⟩
      | Ok value =>
        cases value
        have typed := typing rfl
        have mapSize : currentInst.types.val.length = index.val := by
          have lengths := typed.length_eq
          simpa [List.length_take, Nat.min_eq_left indexBound] using lengths.symm
        have maximum := seed.module.module.env.types.property
        have room : currentInst.types.length < Usize.max := by change currentInst.types.val.length < Usize.max; omega
        have actualBound : index.val < currentInst.module.module.env.types.val.length := by simpa only [source] using within
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        have reached := trace rfl
        obtain ⟨⟨status,after,nextInst⟩,called,effect⟩ := WP.spec_imp_exists
          (add_instance_type_effect memory allocator law current currentInst index actualBound bound room)
        rw [called]
        simp only [bind_ok,uncurry_apply_pair]
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound⟩ := effect.context bound
        have afterExact : after = {before with types := after.types, signature_values := after.signature_values} := by
          calc
            after = {current with types := after.types, signature_values := after.signature_values} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with types := nextInst.types} := by
          calc
            nextInst = {currentInst with types := nextInst.types} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound, ?_, ?_, ?_, ?_, ?_⟩
        · omega
        · intro success
          have extended := effect.entries success typed
          rw [increment, List.take_succ_eq_append_getElem within]
          simpa only [source] using extended
        · intro success
          subst status
          exact .next reached called increment
        · intro error rejected
          subst status
          obtain ⟨ty,found,unchanged,sameInst,absent,refusal⟩ :=
            add_type_resource_cause memory allocator law current currentInst index bound error after nextInst called
          subst after
          subst nextInst
          exact ⟨current,currentInst,index,ty,reached,found,called,absent,refusal⟩
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.types.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged, mapChanged, prefixStore, bound, ?_, cause⟩
      intro success
      simpa only [atEnd, List.take_length] using typing success
  · exact ⟨changed, instChanged, retained, objectBound, startBound, (fun _ => entries), (fun _ => .refl _ _), by simp⟩

end Itasca.Runtime.Store
