import Exec.Code.Body.Reader.Simd.ReaderSimdShuffle
namespace Exec.Code
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
end Exec.Code
