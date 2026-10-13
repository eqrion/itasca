import Itasca.Wasm2.Scalar.ReadersTotal
import Itasca.Visitor.Accepts

/-!
# Totality of SIMD readers

`@[step]` lemmas showing that the extracted SIMD readers (`code.take_simd_bits`,
`code.take_simd_lane`, `code.read_simd_signature`, `code.read_simd_lane`, memory loads and stores,
`code.read_simd_const` and `code.read_simd_shuffle`) never panic. `ReaderPost` is the shared
postcondition: structural shape, unchanged controls, forward cursor and bounded operand growth.
-/

open Aeneas Aeneas.Std

set_option maxHeartbeats 2000000

namespace Itasca.Wasm2.Simd

def ReaderPost (st s : code.OpIterState) : Prop :=
  Control.Shape s ∧ s.ctrls = st.ctrls ∧ st.pos.val ≤ s.pos.val ∧
    s.vals.val.length ≤ st.vals.val.length + 1

attribute [local step] code.pop_with_type.total code.pop_stack_type.total
  code.push_val.shape_total ScalarReaders.memarg code.check_memory_and_alignment.spec

@[local step] private theorem conversion_total (st : code.OpIterState) (input output : types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_conversion st input output ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_conversion ReaderPost
  step*

@[local step] private theorem binary_total (st : code.OpIterState) (input output : types.ValueType)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_binary st input output ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_binary ReaderPost
  step*

@[local step] private theorem byte_total (data : Slice U8) (pos : Usize) :
    reader.read_byte data pos ⦃ _ => True ⦄ := by
  by_cases hp : pos.val < data.length
  · exact WP.spec_mono (reader.read_byte.spec data pos hp) (by simp)
  · simp [reader.read_byte.eof data pos (by omega)]

@[local step] private theorem bits_forward (data : Slice U8) (pos : Usize) :
    reader.read_f64_bits data pos ⦃ r => match r with
      | .Ok (_, next) => pos.val ≤ next.val
      | .Err _ => True ⦄ := by
  apply WP.spec_mono (reader.read_f64_bits.spec data pos)
  intro r hr
  cases r with
  | Err _ => trivial
  | Ok pair => obtain ⟨bytes, _, hn, _⟩ := hr; omega

@[step] theorem take_bits_total (st : code.OpIterState) (data : Slice U8) (hs : Control.Shape st) :
    code.take_simd_bits st data ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals = st.vals ⦄ := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (bits_forward data st.pos)
  cases r with
  | Err e =>
    simp [code.take_simd_bits, hr, hs, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok pair =>
    obtain ⟨low, middle⟩ := pair
    obtain ⟨r, hr2, hp2⟩ := WP.spec_imp_exists (bits_forward data middle)
    cases r with
    | Err e =>
      simp [code.take_simd_bits, hr, hr2, hs, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok pair =>
      obtain ⟨high, last⟩ := pair
      simp only [code.take_simd_bits, hr, hr2, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, Std.uncurry, WP.spec_ok]
      exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩

@[step] theorem lane_total (st : code.OpIterState) (data : Slice U8) (count : U8)
    (hs : Control.Shape st) :
    code.take_simd_lane st data count ⦃ r => Control.Shape r.2 ∧ r.2.ctrls = st.ctrls ∧
      st.pos.val ≤ r.2.pos.val ∧ r.2.vals = st.vals ⦄ := by
  by_cases hp : st.pos.val < data.length
  · obtain ⟨_, hr, next, rfl, hn⟩ := WP.spec_imp_exists (reader.read_byte.spec data st.pos hp)
    simp only [code.take_simd_lane, hr, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [Std.uncurry]
    split <;> simp only [WP.spec_ok] <;> exact ⟨⟨hs.ordered, hs.bounded⟩, trivial, by omega, trivial⟩
  · simp [code.take_simd_lane, reader.read_byte.eof data st.pos (by omega), hs,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem signature_total (st : code.OpIterState) (sig : code.SimdSignature)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_signature st sig ⦃ r => ReaderPost st r.2 ⦄ := by
  cases sig <;> unfold code.read_simd_signature
  all_goals step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem read_lane_total (st : code.OpIterState) (data : Slice U8)
    (ty : types.ValueType) (count : U8) (replace : Bool)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_lane st data ty count replace ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_lane ReaderPost
  step* <;> simp_all [ReaderPost] <;> omega

@[step] theorem memory_lane_total (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (alignment : U32) (store : Bool) (count : U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_memory_lane st data env alignment store count ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_memory_lane ReaderPost
  step*

@[step] theorem load_total (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ty : types.ValueType) (alignment : U32)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_load st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_load ReaderPost
  step*

@[step] theorem store_total (st : code.OpIterState) (data : Slice U8) (env : module.Env)
    (ty : types.ValueType) (alignment : U32)
    (hs : Control.Shape st) :
    code.read_store st data env ty alignment ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_store ReaderPost
  step*

@[step] theorem constant_total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_const st data ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_const ReaderPost
  step*

@[local step] private theorem shuffle_loop_total (st : code.OpIterState) (data : Slice U8)
    (pos : Usize) (i : I32) (hi : 0 ≤ i.val ∧ i.val ≤ 16)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_shuffle_loop st.vals st.ctrls st.pos data pos i ⦃ r => ReaderPost st r.2 ⦄ := by
  unfold code.read_simd_shuffle_loop
  apply loop.spec_decr_nat (fun p => (16 - p.2.val).toNat)
    (fun p => 0 ≤ p.2.val ∧ p.2.val ≤ 16)
  · rintro ⟨pos, i⟩ ⟨hi, hn⟩
    unfold code.read_simd_shuffle_loop.body
    step* <;> simp_all [ReaderPost]
    all_goals try (cases val; step* <;> simp_all)
    all_goals scalar_tac
  · exact hi

@[step] theorem shuffle_total (st : code.OpIterState) (data : Slice U8)
    (hs : Control.Shape st) (hsize : st.vals.val.length < Usize.max) :
    code.read_simd_shuffle st data ⦃ r => ReaderPost st r.2 ⦄ :=
  shuffle_loop_total st data st.pos 0#i32 (by decide) hs hsize

end Itasca.Wasm2.Simd
