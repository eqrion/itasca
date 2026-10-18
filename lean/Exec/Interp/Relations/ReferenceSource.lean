import Exec.Interp.Relations.ReferenceNull
import Exec.Interp.Relations.WordEncoding
import Exec.Spec.References
namespace Exec.Interp
open Aeneas Aeneas.Std SpecExt Exec.Store

/-- The complete raw reference word uses exactly zero for either null type. -/
theorem decode_ref_is_null (ty : Itasca.types.ElemType) (word : U64) :
    Spec.referenceIsNull (decodeRef ty word) = if word = 0#u64 then 1 else 0 := by
  have zero : word = 0#u64 ↔ word.val = 0 := by scalar_tac
  by_cases null : word.val = 0 <;> cases ty <;> simp [decodeRef,decodeElemType,Spec.referenceIsNull,zero,null]

/-- Every raw reference, including the largest encoded address, re-encodes
without loss. Address validity is a separate store invariant. -/
theorem encode_decoded_ref (ty : Itasca.types.ElemType) (word : U64) :
    Code.encodeValue (refVal (decodeRef ty word)) = [word.val] := by
  cases ty
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .FuncRef word 0#u64 (by simp)
  · simpa only [decodeWords,pairWords,sourceType,reduceCtorEq,ite_false] using encode_decode_words .ExternRef word 0#u64 (by simp)

/-- The extracted null test produces the exact canonical Boolean whose source
instruction has the generated pure transition. -/
theorem ref_is_null_source_effect {M P F A : Type}
    (memory : runtime.platform.MemoryBuffer M) (hooks : runtime.platform.Platform P M)
    (floats : runtime.platform.FloatOps F) (allocator : runtime.platform.Alloc A)
    (exec : runtime.interp.Execution) (base : Usize) (dst src : U32)
    (ty : Itasca.types.ElemType) (s : _root_.store) (ambient : frame)
    (sourceBound : base.val+src.val < exec.slots.length)
    (destinationBound : base.val+dst.val < exec.slots.length)
    (storeWf : wf_store s) (ambientWf : wf_frame ambient) :
    runtime.interp.admin_ref_is_null memory hooks floats allocator exec base dst src ⦃ out =>
      out.1 = .Ok () ∧ ∃ result : U64,
        result.val = Spec.referenceIsNull (decodeRef ty exec.slots.val[base.val+src.val]!) ∧
        SlotsEffect exec out.2 (exec.slots.val.set (base.val+dst.val) result) ∧
        StepH ⟨⟨s,ambient⟩,[admininstr_ref (decodeRef ty exec.slots.val[base.val+src.val]!),.REF_IS_NULL]⟩ []
          ⟨⟨s,ambient⟩,[Spec.Segment.i32 result.val]⟩ ⦄ := by
  apply WP.spec_mono (ref_is_null_effect memory hooks floats allocator exec base dst src sourceBound destinationBound)
  intro out effect
  obtain ⟨success,written⟩ := effect
  let result : U64 := if exec.slots.val[base.val+src.val]! = 0#u64 then 1#u64 else 0#u64
  have resultValue : result.val = Spec.referenceIsNull (decodeRef ty exec.slots.val[base.val+src.val]!) := by
    rw [decode_ref_is_null]
    dsimp only [result]
    split <;> rfl
  exact ⟨success,result,resultValue,written,resultValue ▸ Spec.ref_is_null_step s ambient _ storeWf ambientWf⟩
end Exec.Interp
