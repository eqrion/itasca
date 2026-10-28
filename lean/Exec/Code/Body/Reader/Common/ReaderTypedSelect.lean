import Exec.Code.Body.Reader.Simd.ReaderSimdLane
import Itasca.Wasm2.References.Step

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.ResultFacts

/-- The explicit-select reader retains its literal declared type, exact
callback, validated stack effect, and independently decoded source prefix. -/
theorem reader_typed_select_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {V : Type} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (byte : data.val[p.start.val]'p.inbounds = 28#u8)
    (accepted : code.step_profile visitor st data env ctx index .Wasm2 28#u8 before =
      .ok (.Ok (),out,after)) :
    ∃ ty position, visitor.on_select_typed before out.core ty = .ok (.Ok (),after) ∧
      Wasm2.Simd.readFixed {st.core with pos := position} [.I32,ty,ty] (some ty) =
        .ok (.Ok (),out.core) ∧
      out.core.ctrls = st.core.ctrls ∧ out.core.pos = position ∧
      ∃ values, Wasm2.Simd.FixedEffect p.current.ctrl.polymorphic_base p.current.vals
        [.I32,ty,ty] (some ty) values ∧
        ReaderPostWasm2 p out.core (.SELECT (some [Translate.valueType ty])) p.current.ctrl.polymorphic_base values := by
  obtain ⟨capacity,run⟩ := profile_scalar_success visitor st out data env ctx index 28#u8 before after (by decide) accepted
  rw [code.step_wasm2.typed_select] at run
  obtain ⟨selected,read,callback⟩ := reader_run_success _ _ _ _ _ run
  rw [code.read_typed_select.fixed] at read
  obtain ⟨⟨reply,parsed⟩,decode,values,controls,typeInfo⟩ := WP.spec_imp_exists (Wasm2.selectType.spec st.core data)
  dsimp only at values controls typeInfo
  cases reply with
  | Err error => simp [Wasm2.metadataOperands,decode] at read
  | Ok ty =>
    simp only [Wasm2.metadataOperands,decode,bind_ok] at read
    obtain ⟨⟨result,checked⟩,fixed,final⟩ := bind_ok_inv _ _ _ read
    cases result with
    | Err error => simp [uncurry_apply_pair] at final
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair,id_eq,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] at final
      obtain ⟨rfl,rfl⟩ := final
      have parsedEq : parsed = {st.core with pos := parsed.pos} := Wasm2.Simd.state_of_stacks parsed st.core values controls
      rw [parsedEq] at fixed
      obtain ⟨count,bytes,encoding⟩ := typeInfo ty rfl
      have encoded : Wasm2.At data p.start (.plain (.SELECT (some [Translate.valueType ty]))) parsed.pos :=
        Wasm2.At.of_immediate p.inbounds byte p.pos (.reference (.selectTyped ty encoding)) bytes
      refine ⟨ty,parsed.pos,callback,fixed,?_⟩
      exact reader_simd_fixed_post p parsed.pos out.core _ _ _ capacity (.instr_case_3 _)
        (by simp [DeclaredReferences.Instruction,DeclaredReferences.instructionIndices])
        (fun C wf _ => by simpa [Wasm2.Simd.inputTypes,Wasm2.Simd.outputTypes,Translate.valueType]
          using Instr_ok.select_expl C (Translate.valueType ty) wf (.instr_case_3 _)) encoded fixed

end Itasca.Runtime.Code
