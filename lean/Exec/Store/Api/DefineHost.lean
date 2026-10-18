import Exec.Store.Invariant.InternTypes

namespace Exec.Store
open Aeneas Aeneas.Std

/-- Adding a host function keeps all old function references valid and assigns
an existing canonical signature to the new function. -/
theorem Shape.append_host {M : Type} (view : M → Slice U8)
    (s : runtime.store.Store M) (hs : Shape view s) (signature : Usize) (identity : U64)
    (functions : alloc.vec.Vec runtime.store.Function)
    (hfunctions : functions.val = s.funcs.val ++ [{signature, code := .Host identity}])
    (hsignature : signature.val < s.types.length)
    (hroom : objectCount s < s.limits.max_objects.val) :
    Shape view {s with funcs := functions} := by
  have hlen : s.funcs.length ≤ functions.length := by simp [hfunctions]
  constructor
  · exact hs.identity
  · intro function hfunction
    rw [hfunctions] at hfunction
    rcases List.mem_append.mp hfunction with old | fresh
    · simpa [FunctionShape] using hs.functions function old
    · simp only [List.mem_singleton] at fresh
      subst function
      exact ⟨hsignature, trivial⟩
  · exact hs.memories
  · intro table htable
    exact TableShape.mono s {s with funcs := functions} hlen (by simp) table (hs.tables table htable)
  · intro global hglobal
    exact GlobalShape.mono s {s with funcs := functions} hlen (by simp) global (hs.globals global hglobal)
  · intro element helement word hword
    exact ReferenceShape.mono s {s with funcs := functions} hlen (by simp) _ _ (hs.elements element helement word hword)
  · intro inst hinst
    exact InstanceShape.mono s {s with funcs := functions} rfl
      (by simp) hlen (by simp) (by simp) (by simp) (by simp) (by simp)
      inst (hs.instances inst hinst)
  · exact hs.canonicalTypes
  · simp only [alloc.vec.Vec.length, hfunctions, List.length_append, List.length_singleton]
    unfold objectCount at hroom
    simp only [alloc.vec.Vec.length] at hroom
    omega
  · exact hs.instanceLimit
  · exact hs.instanceAccounting
  · exact hs.instanceItemLimit
  · exact hs.signatureAccounting
  · exact hs.signatureLimit
  · exact hs.memoryAccounting
  · exact hs.memoryLimit
  · exact hs.tableAccounting
  · exact hs.tableLimit

/-- Host definition preserves structural validity even when allocation fails
after a new signature has been interned. -/
theorem define_host_preserves_shape {M A : Type} (ops : runtime.platform.MemoryBuffer M)
    (allocator : runtime.platform.Alloc A) (ha : Platform.AllocCorrect allocator)
    (view : M → Slice U8) (s : runtime.store.Store M) (hs : Shape view s)
    (ty : Itasca.types.FuncType) (identity : U64) :
    runtime.store.Store.define_host_with ops allocator s ty identity ⦃ result => Shape view result.2 ⦄ := by
  unfold runtime.store.Store.define_host_with
  step with intern_type_preserves_shape ops allocator ha view s hs ty as ⟨result, interned, hshape, hlookup⟩
  cases result with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
  | Ok signature =>
    simp [core.result.Result.Insts.CoreOpsTry.branch]
    have hsignature : signature.val < interned.types.length := by
      have h := hlookup signature rfl
      exact List.getElem?_eq_some_iff.mp h |>.1
    have hbound : objectCount interned ≤ Usize.max := by
      have h := hshape.object_count_bound
      scalar_tac
    step with room_spec ops interned hbound as ⟨room, hroom⟩
    rw [hroom]
    by_cases hspace : objectCount interned < interned.limits.max_objects.val
    · simp only [if_pos hspace]
      simp [core.result.Result.Insts.CoreOpsTry.branch]
      obtain ⟨answer, hr⟩ := reserve_wrapper_eq allocator ha interned.funcs 1#usize
      rw [hr]
      cases answer
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]
      · simp
        have hmax : interned.funcs.length < Usize.max := by unfold objectCount at hspace; scalar_tac
        step as ⟨functions, hfunctions⟩
        exact Shape.append_host view interned hshape signature identity functions hfunctions hsignature hspace
    · simp [hspace, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, hshape]

end Exec.Store
