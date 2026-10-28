import Itasca.Runtime.Code.Body.Reader.Common.ReaderProfile
import Itasca.Wasm2.Bulk.Dispatch

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Independent accepted bulk dispatch excludes every unsupported subopcode. -/
theorem source_bulk_supported {V : Type} (source : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (sub : U32) (before after : V)
    (reference : code.step_bulk source st data env sub before = .ok (.Ok (),out,after)) :
    sub.val ∈ [8,9,10,11,12,13,14,15,16,17] := by
  rw [code.step_bulk.eq_runs] at reference
  unfold Wasm2.bulkStep at reference
  split at reference <;> first | decide | simp_all

/-- An accepted miscellaneous prefix has an independently decoded saturating
or bulk subopcode. Decode failure and unsupported bulk cases are excluded by
the source run itself, without any compiler premise. -/
theorem source_misc_prefix {V : Type} (source : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context) (index : U32)
    (before after : V)
    (reference : code.step_profile source st data env ctx index .Wasm2 252#u8 before = .ok (.Ok (),out,after)) :
    ∃ sub next, Leb128.Decoded data st.core.pos sub next ∧
      (sub.val < 8 ∨ sub.val ∈ [8,9,10,11,12,13,14,15,16,17]) := by
  obtain ⟨capacity,raw⟩ := profile_scalar_success source st out data env ctx index 252#u8 before after (by decide) reference
  rw [code.step_wasm2.prefixed] at raw
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Wasm2.wasm2PrefixedStep,read,bind_ok] at raw
  cases result with
  | Err error => simp at raw
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    refine ⟨sub,next,decoded,?_⟩
    by_cases small : sub < 8#u32
    · exact .inl (by scalar_tac)
    · simp only [small,↓reduceIte] at raw
      exact .inr (source_bulk_supported source _ out.core data env sub before after raw)

end Itasca.Runtime.Code
