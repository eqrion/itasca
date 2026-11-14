import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Visitor.BodyReplay
import Itasca.Visitor.Events
import Itasca.Wasm2.Step.Context
import Itasca.Runtime.Compiler.Local.Control.Syntax.BulkAndSaturating
import Itasca.Wasm2.Bulk.Total

/-!
Sections, each formerly its own module: ProfileAgreement, BulkAndSaturatingAcceptance.
-/

/-! ## ProfileAgreement -/

section

/-!
Agreement of shared scalar reader steps across validation profiles.

Main declarations: `profile_scalar_eq` and `profile_base_success_wasm2`. A direct consumer is `Compiler.Body.Reader.Acceptance.ProfileAcceptance`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem profile_scalar_eq {V : Type} (visitor : code.OpVisitor V)
    (st : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes) :
    code.step_profile visitor st data env ctx index opcode before =
      (if alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX then
        .ok (.Err .StackTooLarge, st, before)
      else do
        let (reply, state, after) ← code.step_wasm2 visitor st.core data env ctx opcode before
        let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
        match cf with
        | .Continue _ => .ok (.Ok (), {core := state}, after)
        | .Break residual =>
          let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
            (core.convert.FromSame error.OpError) residual
          .ok (error, {core := state}, after)) := by
  have hok : core.result.Result.Insts.CoreOpsTry.branch
      (.Ok () : core.result.Result Unit error.OpError) = .ok (.Continue ()) := rfl
  simp only [code.step_profile, bind_ok, hok]
  split <;> try rfl
  all_goals exact False.elim (ordinary (by decide))

theorem profile_scalar_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (accepted : code.step_profile visitor st data env ctx index opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step_wasm2 visitor st.core data env ctx opcode before = .ok (.Ok (), out.core, after) := by
  rw [profile_scalar_eq visitor st data env ctx index opcode before ordinary] at accepted
  by_cases full : alloc.vec.Vec.len st.core.vals = core.num.Usize.MAX
  · simp [full] at accepted
  · rw [if_neg full] at accepted
    obtain ⟨⟨reply, state, changed⟩, called, tail⟩ := ResultFacts.bind_ok_inv _ _ _ accepted
    simp only [Std.uncurry] at tail
    cases reply with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at tail
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        Result.ok.injEq, Prod.mk.injEq, true_and] at tail
      obtain ⟨rfl, rfl⟩ := tail
      refine ⟨?_, called⟩
      have length := st.core.vals.property
      have notFull : st.core.vals.val.length ≠ Usize.max := by
        intro equal
        apply full
        apply (UScalar.eq_equiv _ _).mpr
        simpa [core.num.Usize.MAX] using equal
      omega

/-- Successful ordinary Wasm 2 dispatch supplies both the reader capacity
and the exact scalar callback run, with the pending zipper's result context. -/
theorem profile_base_success_wasm2 {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx ctx' : code.Context)
    (index : U32) (opcode : U8) (before after : V)
    (ordinary : opcode.val ∉ Wasm2.controlOpcodes)
    (base : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253])
    (sign : Wasm2.NumericExtensions.signMeaning opcode = none)
    (misc : opcode ≠ code.OP_MISC_PREFIX) (locals : ctx.locals = ctx'.locals)
    (accepted : code.step_profile visitor st data env ctx index opcode before = .ok (.Ok (), out, after)) :
    st.core.vals.val.length < Usize.max ∧
      code.step visitor st.core data env ctx' opcode before = .ok (.Ok (), out.core, after) := by
  obtain ⟨capacity, run⟩ := profile_scalar_success visitor st out data env ctx index opcode before after ordinary accepted
  rw [code.step_wasm2.base _ _ _ _ _ _ _ base,
    code.step_extended.base _ _ _ _ _ _ _ sign misc,
    Wasm2.scalar_context _ _ _ _ ctx ctx' _ _ ordinary locals] at run
  exact ⟨capacity, run⟩

end Itasca.Runtime.Compiler

end

/-! ## BulkAndSaturatingAcceptance -/

section

/-!
Accepted subopcode classification for saturating conversions and the ten bulk operations.

Main declarations: `reader_bulk_accepted_subopcode` and `reader_misc_accepted`. A direct consumer is `Compiler.Body.Reader.Checking.NoncontrolCheckedPrefixWasm2`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual bulk dispatcher accepts only its ten source subopcodes. -/
theorem reader_bulk_accepted_subopcode {V} (visitor : code.OpVisitor V)
    (st out : code.OpIterState) (data : Slice U8) (env : metadata.Env) (sub : U32)
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
    (st out : code.BodyState) (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (before after : V)
    (accepted : code.step_profile visitor st data env ctx index 252#u8 before =
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
end Itasca.Runtime.Compiler

end
