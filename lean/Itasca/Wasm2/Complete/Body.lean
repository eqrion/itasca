import Itasca.Wasm2.Complete.Control
import Itasca.Wasm2.ExecutionContext

open Aeneas Aeneas.Std

namespace Itasca.Wasm2.Completeness

/-- Independent typing starts the body with no operands, even when its type
has parameters. The final end closes the selected multi-result signature. -/
theorem body_of_programs (data : Slice U8) (env : module.Env)
    (locals : alloc.vec.Vec types.ValueType) (index : U32) (ft : types.FuncType)
    (hi : env.types.val[index.val]? = some ft)
    (hparams : ft.params.val.length ≤ 1000) (hresults : ft.results.val.length ≤ 1000)
    (hsize : data.length ≤ limits.MAX_FUNCTION_BYTES.val)
    (hprograms : ∀ tokens ops, Emits tokens ops →
      Program data env ⟨locals, ft.results⟩ index tokens ops)
    (ops : List instr) (hencoding : BodyEncoding data ops)
    (htyped : FunctionTyped env locals ft ops)
    (hdecl : DeclaredReferences.Instructions (env.declared_funcs.val.map (fun i => uN.mk_uN i.val)) ops) :
    code.validate_multi_value_body data env locals index = .ok (.Ok ()) := by
  obtain ⟨tokens, next, hbytes, hfinish, inner, heq, hemits⟩ := hencoding
  subst tokens
  obtain ⟨middle, hinner, hend⟩ := Consumed.split hbytes
  let st := initial index
  let f : Frame st :=
    ⟨⟨[], ⟨.Body, .Empty, .TypeIndex index, 0#usize, false⟩, [], [], rfl, rfl, rfl⟩,
      [], .TypeIndex index, rfl, rfl⟩
  let C := Control.labelContext (ft.results.val.map Translate.valueType) ++ bodyContext env locals ft
  have hmatch : EnvTranslation.Matches env ⟨locals, ft.results⟩ C :=
    (EnvTranslation.Matches.root env ⟨locals, ft.results⟩).enter _
  have hlabels : Labels env st C := by
    intro depth
    cases depth with
    | zero => simp [C, st, initial, Control.labelContext_labels, labelTypes, labelAt, target, outputs, resolve, hi]
    | succ depth => simp [C, st, initial, Control.labelContext_labels, bodyContext,
        EnvTranslation.context, labelTypes, labelAt]
  have hbounds : Bounds data st := by
    constructor <;> simp [st, initial, hsize]
  obtain ⟨s, hrun, hp, hout, _⟩ := hprograms inner ops hemits C st f middle []
    (ft.results.val.map Translate.valueType) hmatch hlabels hbounds hinner
      (Sequence.realizes_default false []) htyped hdecl
  obtain ⟨g, hgp, hgc, hcp, hco, hck, hcb, hcbase, hreal⟩ := hout.next
  obtain ⟨last, hclose, hp', hc', hb', _⟩ := execute_end g data env ⟨locals, ft.results⟩
    index next ft.params.val ft.results.val (by simpa [hp] using hend.single)
    (by simp [hgc, f, inputs, resolve, hi]) (by simp [hgc, f, outputs, resolve, hi])
    (by simp [hck, f]) hreal (by simp [hco, f])
  apply ((hrun.append hclose).change_context ⟨locals, alloc.vec.Vec.new _⟩ rfl).public
    hi hparams hresults hsize
  · simpa [hgp, f] using hb'
  · simpa [hp'] using hfinish

end Itasca.Wasm2.Completeness
