import Itasca.Runtime.Compiler.Body.Reader.Simd.SimdFixed
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement

/-!
Accepted SIMD prefix decoding retains the exact unsigned LEB and the selected independent subopcode dispatch.

Main declarations: `simd_prefix_success` and `reader_simd_pure_wasm2`. A direct consumer is `Compiler.Body.Reader.Simd.SimdLane`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Accepted SIMD prefix decoding retains the exact unsigned LEB and the
selected independent subopcode dispatch. -/
theorem simd_prefix_success {V : Type} (visitor : code.OpVisitor V)
    (st out : code.BodyState) (data : Slice U8) (env : module.Env) (ctx : code.Context)
    (index : U32) (before after : V)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    st.core.vals.val.length < Usize.max ∧ ∃ subopcode next,
      Leb128.Decoded data st.core.pos subopcode next ∧
      Wasm2.Simd.subStep visitor {st.core with pos := next} data env subopcode before =
        .ok (.Ok (),out.core,after) := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  obtain ⟨result,read,decoded⟩ := WP.spec_imp_exists (reader.read_u32_leb.spec data st.core.pos)
  cases result with
  | Err error => simp [Wasm2.Simd.prefixStep,read] at run
  | Ok pair =>
    obtain ⟨subopcode,next⟩ := pair
    simp only [Wasm2.Simd.prefixStep,read,bind_ok] at run
    exact ⟨capacity,subopcode,next,decoded,run⟩

/-- Pure SIMD readers retain the exact supplied source prefix and callback. -/
theorem reader_simd_pure_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (subopcode : U32) (next : Usize) (op : Wasm2.Simd.Operation)
    (decoded : Leb128.Decoded data st.core.pos subopcode next)
    (meaning : Wasm2.Simd.pureMeaning subopcode.val = some op)
    (byte : data.val[p.start.val]'p.inbounds = 0xfd#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 0xfd#u8 before =
      .ok (.Ok (),out,after)) :
    visitor.on_simd before out.core subopcode = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := next} op.signature.popTypes (some op.signature.output) =
        .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = next ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        op.signature.popTypes (some op.signature.output) values ∧
        ReaderPostWasm2 p out.core op.instruction p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after
    (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos subopcode next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.pure visitor _ data env subopcode before op meaning] at run
  obtain ⟨unitValue,read,callback⟩ := reader_run_success _ _ _ _ _ run
  cases unitValue
  rw [Wasm2.Simd.signature_fixed] at read
  have encoded : Wasm2.At data p.start (.plain op.instruction) next := by
    obtain ⟨bytes,first,last,within,leb⟩ := decoded
    apply Wasm2.At.of_immediate p.inbounds byte p.pos (.simd subopcode leb (.pure subopcode op meaning))
    simpa only [List.append_nil] using
      (show Wasm1.BytesAt data st.core.pos bytes next from ⟨first,last,within⟩).append
        (Wasm1.BytesAt.nil data next within)
  refine ⟨callback,read,?_⟩
  exact reader_simd_fixed_post p next out.core op.signature.popTypes (some op.signature.output)
    op.instruction capacity op.wellFormed (op.declared _)
    (fun C wf _ => by simpa only [Wasm2.Simd.Signature.inputs_pop,Wasm2.Simd.Signature.outputs_pop]
        using op.typed C wf) encoded read

end Itasca.Runtime.Code
