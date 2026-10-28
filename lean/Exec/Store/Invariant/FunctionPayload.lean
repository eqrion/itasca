import Exec.Store.Invariant.FunctionStaging
import Mathlib.Data.List.Forall2
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
