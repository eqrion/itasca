import Itasca.Runtime.Code.Body.Relations.Common.EntrySignatures
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The captured table supplies an actual readable signature at every canonical
source type index; its parameter width is derived from the captured sequence. -/
theorem SignatureSequence.indirect_call {signatures : Slice runtime.compiler.Signature}
    {types : List Itasca.types.FuncType} (sequence : SignatureSequence signatures.val types)
    (index : U32) (params results : List valtype)
    (source : (types.map Itasca.EnvTranslation.funcType)[index.val]? = some ⟨.mk_list params,.mk_list results⟩) :
    ∃ signature, Slice.index_usize signatures (UScalar.cast .Usize index) = .ok signature ∧
      SignatureMatches signature params results := by
  have inBounds : index.val < types.length := by
    have found := (List.getElem?_eq_some_iff.mp source).1
    simpa using found
  have signatureBound : index.val < signatures.val.length := by
    rw [List.Forall₂.length_eq sequence]; exact inBounds
  let signature := signatures.val[index.val]
  have found : signatures.val[index.val]? = some signature := List.getElem?_eq_getElem signatureBound
  obtain ⟨input,output,lookup,matched⟩ := sequence.table index.val signature found
  have same : params = input ∧ results = output := by
    rw [source] at lookup
    simpa only [Option.some.injEq,functype.mk_functype.injEq,list.mk_list.injEq] using lookup
  obtain ⟨r,read,result⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec signatures (UScalar.cast .Usize index) (by simpa using signatureBound))
  refine ⟨signature,?_,?_⟩
  · have equal : r = signature := by simpa [signature] using result
    simpa only [equal] using read
  · simpa only [same.1,same.2] using matched
end Itasca.Runtime.Code
