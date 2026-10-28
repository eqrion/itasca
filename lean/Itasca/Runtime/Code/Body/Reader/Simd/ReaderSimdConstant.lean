import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdLane
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- An accepted vector constant retains all sixteen encoded bytes, its exact
compiler callback, and the complete independently typed source prefix. -/
theorem reader_simd_constant_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (next : Usize) (decoded : Leb128.Decoded data st.core.pos 12#u32 next)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ low high position, Wasm2.Simd.BitsDecoded data next low high position ∧
      visitor.on_simd_const before out.core low high = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [] (some .V128) = .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals [] (some .V128) values ∧
        ReaderPostWasm2 p out.core (Wasm2.Simd.vectorConstant low high) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos 12#u32 next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.constant] at run
  obtain ⟨⟨low,high⟩,read,callback⟩ := reader_run_success _ _ _ _ _ run
  rw [Wasm2.Simd.const_fixed] at read
  obtain ⟨⟨reply,middle⟩,take,controls,values,bits⟩ := WP.spec_imp_exists
    (Wasm2.Simd.take_bits_spec {st.core with pos := next} data)
  dsimp only at controls values bits
  cases reply with
  | Err error => simp [Wasm2.Simd.constReader,take] at read
  | Ok pair =>
    simp only [Wasm2.Simd.constReader,take,bind_ok,uncurry_apply_pair] at read
    obtain ⟨pairEq,fixed⟩ := simd_carry_success pair (low,high) middle out.core _ _ read
    subst pair
    have bitSpan := bits low high rfl
    have middleEq : middle = {st.core with pos := middle.pos} := Wasm2.Simd.state_of_stacks middle st.core values controls
    rw [middleEq] at fixed
    have encoded : Wasm2.At data p.start (.plain (Wasm2.Simd.vectorConstant low high)) middle.pos := by
      obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
      obtain ⟨lower,upper,lo,hi,span⟩ := bitSpan
      exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd 12#u32 leb (.constant low high lo hi))
        ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append span)
    refine ⟨low,high,middle.pos,bitSpan,callback,fixed,?_⟩
    exact reader_simd_fixed_post p middle.pos out.core [] (some .V128) _ capacity
      (Wasm2.Simd.vectorConstant_wf low high) (Wasm2.Simd.vectorConstant_declared _ low high)
      (fun C wf _ => Wasm2.Simd.vectorConstant_typed C low high wf) encoded fixed
end Itasca.Runtime.Code
