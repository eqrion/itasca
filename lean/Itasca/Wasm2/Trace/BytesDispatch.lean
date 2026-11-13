import Itasca.Wasm2.Trace.BytesSimd
import Itasca.Wasm2.Trace.BytesScalar

/-!
# Byte provenance for the Wasm 2.0 dispatcher

`wasm2_dispatch` combines the reference, bulk and SIMD byte traces with a scalar contract for the
remaining opcodes. `wasm2_scalar` discharges that contract, giving an exact independent callback
byte trace for every non-control step of `code.step_wasm2`.
-/

open Aeneas Aeneas.Std
namespace Itasca.Wasm2.CallbackBytes
open VisitorTrace CallbackTrace

/-- Assembles `code.step_wasm2` dispatch from a contract for the scalar opcodes; the reference,
bulk and SIMD cases are discharged here. -/
theorem wasm2_dispatch {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode)
    (extended : ∀ (op : U8), op.val ∉ controlOpcodes →
      data.val[p.start.val]'p.inbounds = op →
      ∀ v result final v', code.step_extended visitor st.core data env ctx op v =
        .ok (result, final, v') →
        ∃ observations, observe v' = observe v ++ observations ∧
          CallbackTrace.StepTrace data p.start observations result final) :
    StepRecords p visitor observe ctx opcode := by
  by_cases h253 : opcode = 253#u8
  · rw [h253] at hbyte ⊢
    exact simd p visitor observe records ctx hsize hbyte
  by_cases h28 : opcode = 28#u8
  · rw [h28] at hbyte ⊢
    exact typed_select p visitor observe records ctx hsize hbyte
  by_cases h37 : opcode = 37#u8
  · rw [h37] at hbyte ⊢
    exact table_get p visitor observe records ctx hsize hbyte
  by_cases h38 : opcode = 38#u8
  · rw [h38] at hbyte ⊢
    exact table_set p visitor observe records ctx hsize hbyte
  by_cases h208 : opcode = 208#u8
  · rw [h208] at hbyte ⊢
    exact ref_null p visitor observe records ctx hsize hbyte
  by_cases h209 : opcode = 209#u8
  · rw [h209] at hbyte ⊢
    exact ref_is_null p visitor observe records ctx hsize hbyte
  by_cases h210 : opcode = 210#u8
  · rw [h210] at hbyte ⊢
    exact ref_func p visitor observe records ctx hsize hbyte
  by_cases h252 : opcode = 252#u8
  · rw [h252] at hbyte ⊢
    intro v result final v' run
    rw [code.step_wasm2.prefixed] at run
    obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
    simp only [wasm2PrefixedStep, hr, bind_ok] at run
    cases r with
    | Err e =>
      simp only [Result.ok.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨[], by simp, .silent _ _ (Outcomes.empty _)⟩
    | Ok pair =>
      obtain ⟨subopcode, next⟩ := pair
      dsimp only at hd run
      split at run
      · exact extended 252#u8 (by decide) hbyte v result final v' run
      · exact bulk p visitor observe records hbyte next subopcode hd hsize v result final v' run
  have hbase : opcode.val ∉ [28, 37, 38, 208, 209, 210, 252, 253] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    have neq {a b : U8} (h : a ≠ b) : a.val ≠ b.val := fun he => h (UScalar.eq_of_val_eq he)
    exact ⟨neq h28, neq h37, neq h38, neq h208, neq h209, neq h210, neq h252, neq h253⟩
  intro v result final v' run
  rw [code.step_wasm2.base visitor st.core data env ctx opcode v hbase] at run
  exact extended opcode hscalar hbyte v result final v' run

/-- Every non-control Wasm 2.0 step has an exact independent callback byte trace,
including ordinary reader failure and rejecting callbacks. -/
theorem wasm2_scalar {data env locals index st} (p : Pending data env locals index st)
    {V : Type} (visitor : code.OpVisitor V) (observe : V → List Observation)
    (records : Records visitor observe) (ctx : code.Context) (hlocals : ctx.locals = locals)
    (opcode : U8) (hscalar : opcode.val ∉ controlOpcodes)
    (hsize : st.core.vals.val.length < Usize.max)
    (hbyte : data.val[p.start.val]'p.inbounds = opcode) :
    StepRecords p visitor observe ctx opcode := by
  exact wasm2_dispatch p visitor observe records ctx opcode hscalar hsize hbyte
    (fun op hs hb => extended_scalar_records p visitor observe records hsize ctx hlocals op hs hb)

end Itasca.Wasm2.CallbackBytes
