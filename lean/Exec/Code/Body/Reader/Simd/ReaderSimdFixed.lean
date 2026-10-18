import Exec.Code.Body.Reader.Common.ReaderWasm2
import Itasca.Wasm2.Simd.Sound

namespace Exec.Code
open Aeneas Aeneas.Std Itasca

/-- A successful fixed-operand reader retains the supplied source zipper and
its exact operand effect, including polymorphic unreachable stacks. -/
theorem reader_simd_fixed_post {data env locals index st}
    (p : Wasm2.Pending data env locals index st)
    (position : Usize) (out : code.OpIterState)
    (inputs : List types.ValueType) (output : Option types.ValueType) (source : instr)
    (capacity : st.core.vals.val.length < Usize.max)
    (wf : wf_instr source)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) source)
    (typed : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C source (.mk_functype (.mk_list (Wasm2.Simd.inputTypes inputs))
        (.mk_list (Wasm2.Simd.outputTypes output))))
    (encoded : Wasm2.At data p.start (.plain source) position)
    (read : Wasm2.Simd.readFixed {st.core with pos := position} inputs output = .ok (.Ok (),out)) :
    out.ctrls = st.core.ctrls ∧ out.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        inputs output values ∧ ReaderPostWasm2 p out source p.current.ctrl.polymorphic_base values := by
  obtain ⟨C,outer,spine,header,base,prior,ctrls,blocks,stack⟩ := p.opened
  have Cwf := Wasm2.Frames.enter_wf C
    (spine.context_wf (EnvTranslation.context_wf env ⟨locals,p.ft.results⟩))
    p.current.form p.current.ins p.current.outs
  have matched : EnvTranslation.Matches env ⟨locals,p.ft.results⟩
      (Wasm2.Frames.enter C p.current.form p.current.ins p.current.outs) :=
    (spine.matches (EnvTranslation.Matches.root env ⟨locals,p.ft.results⟩)).enter _
  have physicalBase : (Control.base {st.core with pos := position}).val = outer.length := by
    simp [Control.base,ctrls,base]
  have poly : Control.polymorphic {st.core with pos := position} = p.current.ctrl.polymorphic_base := by
    simp [Control.polymorphic,ctrls]
  have effect := Wasm2.Simd.readFixed.segment {st.core with pos := position} inputs output
    outer p.current.vals stack physicalBase capacity
  rw [read,WP.spec_ok] at effect
  obtain ⟨controls,cursor,values,valuesEq,length,fixed⟩ := effect
  dsimp only at controls cursor valuesEq fixed
  have finalEffect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values :=
    by simpa only [poly] using fixed rfl
  have finalTyped := finalEffect.wasm2_prefix _ Cwf _ p.current.ops source prior wf (typed _ Cwf matched)
  have finalEncoded : Wasm2.At data p.start (.plain source) out.pos := cursor ▸ encoded
  have finalControls : out.ctrls.val = p.parents.map Wasm2.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa only [controls] using ctrls
  have finalBlocks : ({st with core := out} : code.BodyState).blocks.val =
      p.parents.map Wasm2.Frames.Saved.bt ++ [p.current.bt] := by simpa [controls,ctrls] using blocks
  refine ⟨controls,cursor,values,finalEffect,finalEncoded,?_,?_⟩
  · exact ⟨C,outer,spine,⟨header.kind,header.placeholder,header.inputs,header.outputs,
      header.prior,.simple header.emits (.plain source wf)⟩,base,finalTyped,finalControls,finalBlocks,valuesEq⟩
  · exact p.append_result C outer spine header base {st with core := out} source
      p.current.ctrl.polymorphic_base values wf finalEncoded finalTyped finalControls finalBlocks valuesEq declared

end Exec.Code
