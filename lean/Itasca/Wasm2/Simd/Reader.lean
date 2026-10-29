import Itasca.Wasm2.Scalar.ReaderPost
import Itasca.Wasm2.Simd.Operands

/-!
Shared exact source-prefix and operand effects for all fixed-operand SIMD readers.
Validator preservation projects the total reader specification; compiler inversion
retains the same read state and stack effect without any visitor premise.
-/
namespace Itasca.Wasm2
open Aeneas Aeneas.Std Itasca

theorem Pending.fixed_reader {data env profile locals index st}
    (p : Wasm2.Pending data env profile locals index st)
    (position : Usize)
    (inputs : List types.ValueType) (output : Option types.ValueType) (source : instr)
    (capacity : st.core.vals.val.length < Usize.max)
    (wf : wf_instr source)
    (declared : DeclaredReferences.Instruction
      (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) source)
    (typed : ∀ C, wf_context C → EnvTranslation.Matches env ⟨locals,p.ft.results⟩ C →
      Instr_ok C source (.mk_functype (.mk_list (Wasm2.Simd.inputTypes inputs))
        (.mk_list (Wasm2.Simd.outputTypes output))))
    (encoded : Wasm2.At data p.start (.plain source) position)
    (hwasm2 : profile ≠ .Wasm1) :
    Wasm2.Simd.readFixed {st.core with pos := position} inputs output ⦃ r =>
      r.2.ctrls = st.core.ctrls ∧ r.2.pos = position ∧
      ∀ unit, r.1 = .Ok unit → ∃ values,
        Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values ∧
        Wasm2.ReaderPost p r.2 source p.current.ctrl.polymorphic_base values ⦄ := by
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
  apply WP.spec_mono (Wasm2.Simd.readFixed.segment {st.core with pos := position} inputs output
    outer p.current.vals stack physicalBase capacity)
  rintro ⟨result,out⟩ ⟨controls,cursor,values,valuesEq,length,fixed⟩
  dsimp only at controls cursor valuesEq fixed
  refine ⟨controls,cursor,?_⟩
  intro unit accepted
  cases unit
  dsimp only at accepted
  subst result
  have finalEffect : Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals inputs output values :=
    by simpa only [poly] using fixed rfl
  have finalTyped := finalEffect.wasm2_prefix _ Cwf _ p.current.ops source prior wf (typed _ Cwf matched)
  have finalEncoded : Wasm2.At data p.start (.plain source) out.pos := cursor ▸ encoded
  have finalControls : out.ctrls.val = p.parents.map Wasm2.Frames.Saved.ctrl ++
      [{p.current.ctrl with polymorphic_base := p.current.ctrl.polymorphic_base}] := by
    simpa only [controls] using ctrls
  have finalBlocks : ({st with core := out} : code.BodyState).blocks.val =
      p.parents.map Wasm2.Frames.Saved.bt ++ [p.current.bt] := by simpa [controls,ctrls] using blocks
  refine ⟨values,finalEffect,?_⟩
  exact p.append_reader_context C outer spine header base out source
    p.current.ctrl.polymorphic_base values wf finalEncoded finalTyped finalControls finalBlocks valuesEq
    declared (fun hp => absurd hp hwasm2)

theorem Pending.fixed_reader_accepted {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st)
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
        inputs output values ∧ Wasm2.ReaderPost p out source p.current.ctrl.polymorphic_base values := by
  have effect := p.fixed_reader position inputs output source capacity wf declared typed encoded (by intro h; cases h)
  rw [read, WP.spec_ok] at effect
  exact ⟨effect.1, effect.2.1, effect.2.2 () rfl⟩

end Itasca.Wasm2
