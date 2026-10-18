import Exec.Store.Invariant.SemanticApi
import Exec.Store.Invariant.Syntax
import Exec.Spec.Mutation
namespace Exec.Store
open Aeneas Aeneas.Std

/-- A typed, owned write to an existing mutable global preserves structural
validity and extends the decoded store in the generated specification. -/
theorem global_write_extends {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (shape : Shape view s) (sourceSyntax : StoreSyntax code s)
    (index : Usize) (value : runtime.Value)
    (hindex : index.val < s.globals.length)
    (hmutable : (s.globals.val[index.val]).ty.mutability = .Var)
    (htype : (s.globals.val[index.val]).ty.valtype = Interp.rawType value)
    (owned : ValueInStore s value) :
    runtime.store.Store.set_global ops s ⟨s.id, index⟩ value ⦃ answer =>
      answer.1 = .Ok () ∧ Shape view answer.2 ∧ StoreSyntax code answer.2 ∧
      Extend_store (decodeStore view code s) (decodeStore view code answer.2) ⦄ := by
  obtain ⟨answer, returned, freshShape⟩ := WP.spec_imp_exists
    (global_write_preserves_shape ops view s shape index value hindex hmutable htype owned)
  have effect := global_write ops s index value hindex hmutable htype owned.1
  rw [returned] at effect ⊢
  simp only [WP.spec_ok] at effect ⊢
  obtain ⟨words, encoded, represented, same⟩ := effect
  rw [same] at freshShape ⊢
  let fresh := {s with globals := (s.globals.set index
    {s.globals.val[index.val] with lo := words.1, hi := words.2})}
  have freshSyntax : StoreSyntax code fresh := sourceSyntax
  have oldWf := decodeStore_wf view code s shape sourceSyntax
  have freshWf := decodeStore_wf view code fresh freshShape freshSyntax
  refine ⟨rfl, freshShape, freshSyntax, ?_⟩
  have objectExtension : Extend_globalinst (decodeGlobal s.globals.val[index.val])
      (decodeGlobal {s.globals.val[index.val] with lo := words.1, hi := words.2}) := by
    unfold decodeGlobal
    rw [hmutable]
    exact Spec.extend_global_mutable _ _ _
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
      (.globalinst_case_ _ _ (decodeWords_wf _ _ _))
  dsimp only [Prod.snd]
  rw [decodeStore_global_update view code s (s.globals.set index
    {s.globals.val[index.val] with lo := words.1, hi := words.2})]
  simp only [alloc.vec.Vec.set_val_eq, List.map_set]
  apply Spec.extend_store_set_global _ _ _ oldWf
  · change wf_store (decodeStore view code {s with globals := (s.globals.set index
      {s.globals.val[index.val] with lo := words.1, hi := words.2})}) at freshWf
    rw [decodeStore_global_update view code s (s.globals.set index
      {s.globals.val[index.val] with lo := words.1, hi := words.2})] at freshWf
    simpa only [decodeStore, alloc.vec.Vec.set_val_eq, List.map_set] using freshWf
  · intro bound
    simpa only [decodeStore, getElem!_pos (s.globals.val.map decodeGlobal) index.val (by simpa only [List.length_map] using hindex),
      List.getElem_map] using objectExtension
end Exec.Store
