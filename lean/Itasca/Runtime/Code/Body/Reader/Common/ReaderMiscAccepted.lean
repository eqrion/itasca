import Itasca.Runtime.Code.Local.Control.Common.CumulativeMiscSupport
import Itasca.Runtime.Code.Body.Reader.Common.ReaderProfile
import Itasca.Wasm2.Bulk.Dispatch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- The actual bulk dispatcher accepts only its ten source subopcodes. -/
theorem reader_bulk_accepted_subopcode {V} (visitor : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : module.Env) (sub : U32)
    (before after : V)
    (accepted : code.step_bulk visitor st data env sub before = .ok (.Ok (),out,after)) :
    sub.val ∈ [8,9,10,11,12,13,14,15,16,17] := by
  rw [code.step_bulk.eq_runs] at accepted
  unfold Wasm2.bulkStep at accepted
  split at accepted <;> first | decide | simp_all

theorem cumulative_misc_small (sub : U32) (small : sub.val < 8) : CumulativeMiscOpcode sub := by
  have meaning : ∃ operation, Wasm2.NumericExtensions.saturatingMeaning sub = some operation := by
    rcases sub with ⟨⟨value,bound⟩⟩
    change value < 8 at small
    interval_cases value <;> exact ⟨_,rfl⟩
  obtain ⟨operation,meaning⟩ := meaning
  obtain ⟨op,extended,number,_⟩ := saturating_float_descriptor meaning
  exact .inl ⟨op,extended,number⟩

/-- Recognition of a misc instruction comes from the actual successful
reader; no independent encoding of the unconsumed suffix is assumed. -/
theorem reader_misc_accepted {V} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (before after : V)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 252#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ sub next, Leb128.Decoded data st.core.pos sub next ∧ CumulativeMiscOpcode sub := by
  obtain ⟨_,run⟩ := profile_scalar_success visitor st out data env ctx index 252#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.prefixed] at run
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  simp only [Wasm2.wasm2PrefixedStep,read,bind_ok] at run
  cases result with
  | Err error => simp at run
  | Ok pair =>
    obtain ⟨sub,next⟩ := pair
    by_cases small : sub < 8#u32
    · exact ⟨sub,next,decoded,cumulative_misc_small sub (by scalar_tac)⟩
    · simp only [if_neg small] at run
      exact ⟨sub,next,decoded,.inr (reader_bulk_accepted_subopcode visitor _ _ data env sub before after run)⟩
end Itasca.Runtime.Code
