import Exec.Store.Invariant.SemanticRead

namespace Exec.Store
open Aeneas Aeneas.Std

/-- An external identity lookup returns precisely the identity retained at its
issued index. Identity payloads are opaque to WebAssembly semantics. -/
theorem extern_identity_read {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (s : runtime.store.Store M) (index : Usize) (hindex : index.val < s.externs.length) :
    runtime.store.Store.extern_identity ops s ⟨s.id, index⟩ ⦃ answer =>
      answer = .Ok s.externs.val[index.val] ⦄ := by
  unfold runtime.store.Store.extern_identity
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨identity, hidentity⟩
  simp [hidentity]

theorem decodeFunction_type {M : Type} (code : CodeInterpretation)
    (s : runtime.store.Store M) (function : runtime.store.Function)
    (hsignature : function.signature.val < s.types.length) :
    (decodeFunction code s function).TYPE = decodeFuncType s.types.val[function.signature.val] := by
  unfold decodeFunction
  dsimp only
  cases function.code <;> simp [List.getElem?_eq_getElem hsignature]
  split <;> rfl

/-- Public function signatures agree with the corresponding decoded function
instance's specification type. -/
theorem function_type_read {M : Type} (ops : runtime.platform.MemoryBuffer M)
    (view : M → Slice U8) (code : CodeInterpretation)
    (s : runtime.store.Store M) (hs : Shape view s)
    (index : Usize) (hindex : index.val < s.funcs.length) :
    runtime.store.Store.func_type ops s ⟨s.id, index⟩ ⦃ answer =>
      ∃ ty, answer = .Ok ty ∧
        decodeFuncType ty = (decodeFunction code s s.funcs.val[index.val]).TYPE ⦄ := by
  unfold runtime.store.Store.func_type
  simp [runtime.store.Store.check, core.result.Result.Insts.CoreOpsTry.branch]
  step as ⟨function, hfunction⟩
  have hsignature := (hs.functions function (by simp [hfunction])).1
  step as ⟨ty, hty⟩
  refine ⟨ty, rfl, ?_⟩
  subst function
  rw [decodeFunction_type code s _ hsignature]
  simp [hty]

end Exec.Store
