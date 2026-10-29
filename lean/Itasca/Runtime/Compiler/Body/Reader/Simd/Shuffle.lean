import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdConstant

/-!
SIMD shuffle reader decoding and fixed-instruction characterization, used by SIMD callback replay.
-/

/-! ## Reader Simd Shuffle -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Shuffle validation retains its checked lane vector, exact source bytes,
compiler callback, and polymorphic operand effect. -/
theorem reader_simd_shuffle_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 13#u32 next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ low high, Wasm2.Simd.BitsDecoded data next low high out.core.pos ∧
      (∀ lane ∈ Wasm2.Simd.shuffleIndices low high, proj_uN_0 lane < 32) ∧
      visitor.on_simd_shuffle before out.core low high = .ok (.Ok (),after) ∧
      code.read_simd_shuffle {st.core with pos := next} data = .ok (.Ok (low,high),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [.V128,.V128] (some .V128) values ∧
        Wasm2.ReaderPost p out.core (Wasm2.Simd.shuffle low high) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos 13#u32 next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.shuffle] at run
  obtain ⟨⟨low,high⟩,read,callback⟩ := CoreVisitor.run.accepted _ _ _ _ _ run
  have within : next.val ≤ data.length := by
    obtain ⟨_, _, _, bound, _⟩ := decoded
    exact bound
  have effect := p.shuffle_reader (by intro h; cases h) next within capacity (by
    intro low high position bits
    obtain ⟨prefixBytes, first, last, within, leb⟩ := decoded
    obtain ⟨lower, upper, lo, hi, span⟩ := bits
    exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd 13#u32 leb (.shuffle low high lo hi))
      ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first, last, within⟩).append span))
  rw [read, WP.spec_ok] at effect
  obtain ⟨bits, bounds, controls, values, operands, post⟩ := effect low high rfl
  exact ⟨low, high, bits, bounds, callback, read, controls, values, operands, post⟩
end Itasca.Runtime.Compiler

end

/-! ## Reader Simd Shuffle Fixed -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The checked shuffle scan is followed by the same fixed operand reader as
the other SIMD families, at the exact final cursor. -/
theorem simd_shuffle_fixed (st out : code.OpIterState) (data : Slice U8)
    (outer segment : List code.StackType) (values : st.vals.val = outer ++ segment)
    (base : (Control.base st).val = outer.length) (capacity : st.vals.val.length < Usize.max)
    (position : st.pos.val ≤ data.length) (low high : U64)
    (accepted : code.read_simd_shuffle st data = .ok (.Ok (low,high),out)) :
    Wasm2.Simd.readFixed {st with pos := out.pos} [.V128,.V128] (some .V128) = .ok (.Ok (),out) := by
  have spec : code.read_simd_shuffle st data ⦃ r => ∀ lo hi, r.1 = .Ok (lo,hi) →
      Wasm2.Simd.readFixed {st with pos := r.2.pos} [.V128,.V128] (some .V128) = .ok (.Ok (),r.2) ⦄ := by
    apply Wasm2.Simd.shuffle_scan st data position
    · intro e; simp
    · intro bytes next span length bounds
      obtain ⟨⟨reply,parsed⟩,take,controls,vals,bits⟩ := WP.spec_imp_exists (Wasm2.Simd.take_bits_spec st data)
      dsimp only at controls vals
      simp only [Wasm2.Simd.shuffleFinish,take,bind_ok,uncurry_apply_pair]
      cases reply with
      | Err error => simp
      | Ok pair =>
        obtain ⟨⟨result,after⟩,read,readControls,cursor,effect⟩ := WP.spec_imp_exists
          (Wasm2.Simd.readFixed.segment parsed [.V128,.V128] (some .V128) outer segment
            (by simpa only [vals] using values) (by simpa only [Control.base,controls] using base)
            (by simpa only [vals] using capacity))
        dsimp only at cursor
        simp only [Wasm2.Simd.carryFixed,read,bind_ok,uncurry_apply_pair]
        cases result with
        | Err error => simp
        | Ok unitValue =>
          cases unitValue
          simp only [WP.spec_ok]
          intro lo hi success
          have parsedEq : parsed = {st with pos := after.pos} := by
            rw [cursor]
            exact Wasm2.Simd.state_of_stacks parsed st vals controls
          simpa only [parsedEq] using read
  rw [accepted,WP.spec_ok] at spec
  exact spec low high rfl
end Itasca.Runtime.Compiler

end
