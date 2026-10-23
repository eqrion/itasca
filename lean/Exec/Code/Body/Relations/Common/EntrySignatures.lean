import Exec.Code.Local.Relations.Table.SignatureTable
import Exec.Code.Body.Reader.Common.ReaderEnterWasm2
namespace Exec.Code
open Aeneas.Std Itasca

/-- Concrete block selection agrees with the canonical resolved parameter and
result vectors, including indexed multi-value block signatures. -/
theorem SignatureAt.resolved {signatures bt signature env ins outs}
    (selected : SignatureAt signatures bt signature)
    (table : SignatureTable signatures (env.types.val.map EnvTranslation.funcType))
    (inputs : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs bt) = some outs) :
    SignatureMatches signature (ins.map Translate.valueType) (outs.map Translate.valueType) := by
  cases selected with
  | empty =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins outs
    constructor <;> rfl
  | value ty word bound =>
    simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve] at inputs outputs
    subst ins outs
    constructor <;> simp [slots, bound]
  | index index signature found =>
    obtain ⟨params, results, lookup, matched⟩ := table index.val signature found
    simp only [List.getElem?_map] at lookup
    cases atType : env.types.val[index.val]? with
    | none => simp [atType] at lookup
    | some ty =>
      simp only [atType, Option.map_some, Option.some.injEq, EnvTranslation.funcType,
        functype.mk_functype.injEq, list.mk_list.injEq] at lookup
      simp [Wasm2.inputs, Wasm2.outputs, Wasm2.resolve, atType] at inputs outputs
      subst ins outs
      simpa only [← lookup.1, ← lookup.2] using matched

theorem SignatureSequence.select {signatures : Slice runtime.compiler.Signature} {env bt ins outs}
    (sequence : SignatureSequence signatures.val env.types.val)
    (inputs : Wasm2.resolve env (Wasm2.inputs bt) = some ins)
    (outputs : Wasm2.resolve env (Wasm2.outputs bt) = some outs) :
    ∃ signature, SignatureAt signatures bt signature ∧
      SignatureMatches signature (ins.map Translate.valueType) (outs.map Translate.valueType) := by
  have selected : ∃ signature, SignatureAt signatures bt signature := by
    cases bt with
    | Empty => exact ⟨_, .empty⟩
    | Value ty =>
      have bound : width (Translate.valueType ty) < 2^32 := by cases ty <;> decide
      exact ⟨_, .value ty (UScalar.ofNatCore _ bound) rfl⟩
    | TypeIndex index =>
      have inBounds : index.val < env.types.val.length := by
        by_contra h
        simp [Wasm2.inputs, Wasm2.resolve, List.getElem?_eq_none (by omega : env.types.val.length ≤ index.val)] at inputs
      have sigBounds : index.val < signatures.val.length := by rw [List.Forall₂.length_eq sequence]; exact inBounds
      exact ⟨signatures.val[index.val], .index index _ (List.getElem?_eq_getElem sigBounds)⟩
  obtain ⟨signature, selected⟩ := selected
  exact ⟨signature, selected, selected.resolved sequence.table inputs outputs⟩

end Exec.Code
