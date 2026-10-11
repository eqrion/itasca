import Itasca.MultiValue.SimdBinary
import Itasca.Binary.WasmBinaryComplete
import Itasca.MultiValue.SimdTotal

open Aeneas Aeneas.Std

namespace Itasca.MultiValue.Simd

theorem state_of_stacks (s st : code.OpIterState) (hv : s.vals = st.vals) (hc : s.ctrls = st.ctrls) :
    s = {st with pos := s.pos} := by cases s; cases st; simp_all

/-- Accepted lane bytes satisfy their instruction-specific lane limit. -/
theorem take_lane_spec (st : code.OpIterState) (data : Slice U8) (count : U8) :
    code.take_simd_lane st data count ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.vals = st.vals ∧
      (∀ lane, r.1 = .Ok lane → lane.val < count.val ∧
        Wasm.BytesAt data st.pos [lane] r.2.pos) ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_simd_lane, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [Std.uncurry]
    split
    · simp
    · rename_i hl
      rw [WP.spec_ok]
      refine ⟨rfl, rfl, ?_⟩
      intro lane he
      cases he
      exact ⟨by scalar_tac, Wasm.BytesAt.byte data st.pos next _ hp rfl hn⟩
  · simp [code.take_simd_lane, reader.read_byte.eof data st.pos (by omega),
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem take_lane_complete (st : code.OpIterState) (data : Slice U8) (count lane : U8)
    (next : Usize) (hb : Wasm.BytesAt data st.pos [lane] next) (hl : lane.val < count.val) :
    code.take_simd_lane st data count = .ok (.Ok lane, {st with pos := next}) := by
  have hn : ¬ lane ≥ count := by scalar_tac
  simp [code.take_simd_lane, hb.read_byte, hn, hl, core.result.Result.Insts.CoreOpsTry.branch]

/-- Sixteen accepted bytes split into their exact low and high words. -/
def BitsDecoded (data : Slice U8) (start : Usize) (low high : U64) (next : Usize) : Prop :=
  ∃ lower upper, FloatBits.Encoding 8 lower low.val ∧ FloatBits.Encoding 8 upper high.val ∧
    Wasm.BytesAt data start (lower ++ upper) next

theorem take_bits_spec (st : code.OpIterState) (data : Slice U8) :
    code.take_simd_bits st data ⦃ r => r.2.ctrls = st.ctrls ∧ r.2.vals = st.vals ∧
      (∀ low high, r.1 = .Ok (low, high) → BitsDecoded data st.pos low high r.2.pos) ⦄ := by
  obtain ⟨r, hr, hd⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data st.pos)
  cases r with
  | Err e =>
    simp [code.take_simd_bits, hr, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, middle⟩ := pair
    obtain ⟨r, hr2, hd2⟩ := WP.spec_imp_exists (reader.read_f64_bits.spec data middle)
    cases r with
    | Err e =>
      simp [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨high, last⟩ := pair
      simp only [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, Std.uncurry, WP.spec_ok]
      obtain ⟨lower, hls, hll, hlb, hle⟩ := hd
      obtain ⟨upper, hus, hul, hub, hue⟩ := hd2
      refine ⟨trivial, trivial, ?_⟩
      intro lo hi he
      cases he
      exact ⟨lower, upper, hle, hue,
        (show Wasm.BytesAt data st.pos lower middle from ⟨hls, by simpa [hle.1] using hll, hlb⟩).append
          ⟨hus, by simpa [hue.1] using hul, hub⟩⟩

theorem take_bits_complete (st : code.OpIterState) (data : Slice U8)
    (low high : U64) (lower upper : List U8) (next : Usize)
    (hl : FloatBits.Encoding 8 lower low.val) (hh : FloatBits.Encoding 8 upper high.val)
    (hb : Wasm.BytesAt data st.pos (lower ++ upper) next) :
    code.take_simd_bits st data = .ok (.Ok (low, high), {st with pos := next}) := by
  obtain ⟨middle, hfirst, hlast⟩ := hb.split
  simp [code.take_simd_bits, hfirst.read_f64 low hl, hlast.read_f64 high hh,
    core.result.Result.Insts.CoreOpsTry.branch]

end Itasca.MultiValue.Simd
