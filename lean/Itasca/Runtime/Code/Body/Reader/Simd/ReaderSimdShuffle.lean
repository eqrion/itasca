import Itasca.Runtime.Code.Body.Reader.Simd.ReaderSimdConstant
namespace Itasca.Runtime.Code
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
        ReaderPostWasm2 p out.core (Wasm2.Simd.shuffle low high) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 0xfd#u8 before after (by decide) accepted
  rw [code.step_wasm2.simd,code.step_simd.eq_runs] at run
  have readLeb := reader.read_u32_leb.complete data st.core.pos 13#u32 next decoded
  simp only [Wasm2.Simd.prefixStep,readLeb,bind_ok] at run
  rw [Wasm2.Simd.subStep.shuffle] at run
  obtain ⟨⟨low,high⟩,read,callback⟩ := reader_run_success _ _ _ _ _ run
  obtain ⟨C,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have Cwf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have physicalBase : (Control.base {st.core with pos := next}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have poly : Control.polymorphic {st.core with pos := next} = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic,ctrls]
  obtain ⟨prefixBytes,first,last,within,leb⟩ := decoded
  have spec := Wasm2.Simd.shuffle_segment {st.core with pos := next} data outer p.current.vals stack physicalBase capacity within
  rw [read,WP.spec_ok] at spec
  obtain ⟨controls,values,valuesEq,bits,bounds,effect⟩ := spec low high rfl
  dsimp only at controls valuesEq bits effect
  rw [poly] at effect
  have encoded : Wasm2.At data p.start (.plain (Wasm2.Simd.shuffle low high)) out.core.pos := by
    obtain ⟨lower,upper,lo,hi,span⟩ := bits
    exact Wasm2.At.of_immediate p.inbounds byte p.pos (.simd 13#u32 leb (.shuffle low high lo hi))
      ((show Wasm1.BytesAt data st.core.pos prefixBytes next from ⟨first,last,within⟩).append span)
  have typed := effect.wasm2_prefix _ Cwf _ p.current.ops (Wasm2.Simd.shuffle low high) prior
    (Wasm2.Simd.shuffle_wf low high) (Wasm2.Simd.shuffle_typed _ low high Cwf bounds)
  have finalControls : out.core.ctrls.val = p.parents.map Wasm2.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa only [controls] using ctrls
  have finalBlocks : ({st with core := out.core} : code.BodyState).blocks.val =
      p.parents.map Wasm2.Frames.Saved.bt ++ [p.current.bt] := by simpa [controls,ctrls] using blocks
  refine ⟨low,high,bits,bounds,callback,read,controls,values,effect,encoded,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.inputs,header.outputs,
      header.prior,.simple header.emits (.plain _ (Wasm2.Simd.shuffle_wf low high))⟩,
      base,typed,finalControls,finalBlocks,valuesEq⟩
  · exact p.append_result C outer spine header base {st with core := out.core} _
      p.current.ctrl.polymorphic_base values (Wasm2.Simd.shuffle_wf low high) encoded typed finalControls finalBlocks valuesEq
      (fun h => nomatch h) (Wasm2.Simd.shuffle_declared _ low high)
end Itasca.Runtime.Code
