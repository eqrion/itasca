import Itasca.Runtime.Store.Invariant.FunctionStaging
import Mathlib.Data.List.Forall2
import Itasca.Runtime.Store.Invariant.TypeStaging

/-!
Function allocation payload and its loop preservation. Shared certificates remain independent of the instantiation construction.
-/

/-! ## Function Payload -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- Exact source ordinal and interned type index stored in a freshly allocated
Wasm function. The function body is supplied later by the compiled module's
source interpretation. -/
def FunctionAllocatedAt (seed : runtime.store.ModuleInst) (instanceIndex : Usize)
    (ordinal : Nat) (function : runtime.store.FuncInst) : Prop :=
  ∃ index : Usize, index.val = ordinal ∧ function.code = .Wasm instanceIndex index ∧
    ∃ typeIndex, seed.module.module.env.func_type_indices.val[ordinal]? = some typeIndex ∧
      seed.types.val[typeIndex.val]? = some function.signature

def FunctionPayload {M : Type} (before after : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) (instanceIndex : Usize) (count : Nat) : Prop :=
  ∃ fresh, after.funcs.val = before.funcs.val ++ fresh ∧
    List.Forall₂ (FunctionAllocatedAt seed instanceIndex) (List.range count) fresh

theorem FunctionPayload.initial {M : Type} (store : runtime.store.Store M)
    (seed : runtime.store.ModuleInst) (instanceIndex : Usize) :
    FunctionPayload store store seed instanceIndex 0 := ⟨[], by simp, .nil⟩

theorem FunctionStageEffect.payload {M : Type} {before store : runtime.store.Store M}
    {inst seed : runtime.store.ModuleInst} {instanceIndex index signature out}
    (effect : FunctionStageEffect store inst instanceIndex index signature out)
    (success : out.1 = .Ok ())
    (payload : FunctionPayload before store seed instanceIndex index.val)
    (source : inst.module = seed.module) (types : inst.types = seed.types)
    (bound : index.val < inst.module.module.env.func_type_indices.val.length)
    (typeBound : inst.module.module.env.func_type_indices.val[index.val].val < inst.types.val.length)
    (signatureEq : signature = inst.types.val[inst.module.module.env.func_type_indices.val[index.val].val]) :
    FunctionPayload before out.2.1 seed instanceIndex (index.val + 1) := by
  rcases effect with ⟨error, rfl⟩ | ⟨functions, addresses, appended, mapped, room, rfl⟩
  · simp at success
  · obtain ⟨fresh, stored, paired⟩ := payload
    refine ⟨fresh ++ [{signature, code := .Wasm instanceIndex index}], ?_, ?_⟩
    · simpa only [stored, List.append_assoc] using appended
    · rw [List.range_succ]
      apply List.rel_append paired
      refine .cons ⟨index, rfl, rfl, inst.module.module.env.func_type_indices.val[index.val], ?_, ?_⟩ .nil
      · simpa only [source] using List.getElem?_eq_getElem bound
      · simpa only [types, signatureEq] using List.getElem?_eq_getElem typeBound
end Itasca.Runtime.Store

end

/-! ## Function Payload Loop -/

section

namespace Itasca.Runtime.Store
open Aeneas Aeneas.Std

/-- The actual defined-function allocation loop establishes complete issued
function maps, while retaining all old store objects. The exact helper effect
also records each function's canonical signature and source function index. -/
theorem function_payload_loop {M A : Type} (memory : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (law : Platform.AllocCorrect allocator)
    (before store : runtime.store.Store M) (seed inst : runtime.store.ModuleInst)
    (instanceIndex start : Usize)
    (startBound : start.val ≤ seed.module.module.env.func_type_indices.val.length)
    (changed : store = {before with funcs := store.funcs})
    (instChanged : inst = {seed with funcs := inst.funcs})
    (retained : StagedPrefix before store) (objectBound : objectCount store ≤ Usize.max)
    (typeBounds : ∀ idx ∈ seed.module.module.env.func_type_indices.val, idx.val < seed.types.length)
    (issued : ∀ address ∈ inst.funcs.val, address.index.val < store.funcs.length)
    (count : inst.funcs.length = seed.funcs.length + start.val)
    (capacity : seed.funcs.length + seed.module.module.env.func_type_indices.val.length ≤ Usize.max)
    (payload : FunctionPayload before store seed instanceIndex start.val) :
    runtime.store.instantiate.Store.prepare_instance_loop4 memory allocator store (.Ok ()) start inst instanceIndex
      ⦃ out => ∃ after next status, out = typeParts after status next ∧
        after = {before with funcs := after.funcs} ∧ next = {seed with funcs := next.funcs} ∧
        StagedPrefix before after ∧ objectCount after ≤ Usize.max ∧
        (∀ address ∈ next.funcs.val, address.index.val < after.funcs.length) ∧
        (status = .Ok () → next.funcs.length = seed.funcs.length + seed.module.module.env.func_type_indices.val.length ∧
          FunctionPayload before after seed instanceIndex seed.module.module.env.func_type_indices.val.length) ⦄ := by
  unfold runtime.store.instantiate.Store.prepare_instance_loop4
  apply loop.spec_decr_nat (fun state => seed.module.module.env.func_type_indices.val.length - state.2.2.1.val)
    (fun state => state.1 = {before with funcs := state.1.funcs} ∧
      state.2.2.2 = {seed with funcs := state.2.2.2.funcs} ∧ StagedPrefix before state.1 ∧
      objectCount state.1 ≤ Usize.max ∧
      (∀ address ∈ state.2.2.2.funcs.val, address.index.val < state.1.funcs.length) ∧
      state.2.2.1.val ≤ seed.module.module.env.func_type_indices.val.length ∧
      (state.2.1 = .Ok () → state.2.2.2.funcs.length = seed.funcs.length + state.2.2.1.val ∧
        FunctionPayload before state.1 seed instanceIndex state.2.2.1.val))
  · rintro ⟨current, status, index, currentInst⟩ ⟨currentChanged, mapChanged, prefixStore, bound, currentIssued, indexBound, counting⟩
    dsimp only at currentChanged mapChanged prefixStore bound currentIssued indexBound counting ⊢
    have source : currentInst.module = seed.module := by
      have eq := congrArg runtime.store.ModuleInst.module mapChanged
      exact eq
    have types : currentInst.types = seed.types := by
      have eq := congrArg runtime.store.ModuleInst.types mapChanged
      exact eq
    unfold runtime.store.instantiate.Store.prepare_instance_loop4.body
    simp only [runtime.compiler.ExecutableModule.env, Itasca.module.Module.impl.env, Itasca.module.Env.impl.func_type_indices, source, bind_ok]
    split
    · rename_i more
      have within : index.val < seed.module.module.env.func_type_indices.val.length := by
        simpa [alloc.vec.Vec.deref] using more
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        exact ⟨current, currentInst, .Err error, by simp [typeParts, source], currentChanged,
          mapChanged, prefixStore, bound, currentIssued, by simp⟩
      | Ok value =>
        cases value
        obtain ⟨size, currentPayload⟩ := counting rfl
        have actualBound : index.val < currentInst.module.module.env.func_type_indices.val.length := by simpa only [source] using within
        have typeBound : currentInst.module.module.env.func_type_indices.val[index.val].val < currentInst.types.val.length := by
          simpa only [source, types] using typeBounds _ (List.getElem_mem within)
        have room : currentInst.funcs.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte]
        step with add_instance_function_effect memory allocator law current currentInst instanceIndex index
          bound actualBound typeBound room as ⟨status, after, nextInst, effect⟩
        obtain ⟨afterChanged, nextChanged, prefixNext, nextBound, _⟩ := effect.context bound
        have afterExact : after = {before with funcs := after.funcs} := by
          calc
            after = {current with funcs := after.funcs} := afterChanged
            _ = _ := by rw [currentChanged]
        have nextExact : nextInst = {seed with funcs := nextInst.funcs} := by
          calc
            nextInst = {currentInst with funcs := nextInst.funcs} := nextChanged
            _ = _ := by rw [mapChanged]
        step as ⟨next, increment⟩
        refine ⟨afterExact, nextExact, prefixStore.trans prefixNext, nextBound,
          effect.issued currentIssued, ?_, ?_, ?_⟩
        · omega
        · intro success
          have appended := effect.count success
          dsimp only at appended
          constructor
          · omega
          · rw [increment]
            exact effect.payload success currentPayload source types actualBound typeBound rfl
        · omega
    · rename_i stopped
      have atEnd : index.val = seed.module.module.env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref] at stopped
        omega
      simp only [WP.spec_ok]
      refine ⟨current, currentInst, status, by simp [typeParts, source], currentChanged,
        mapChanged, prefixStore, bound, currentIssued, ?_⟩
      intro success
      simpa only [atEnd] using counting success
  · exact ⟨changed, instChanged, retained, objectBound, issued, startBound, fun _ => ⟨count, payload⟩⟩

end Itasca.Runtime.Store

end
