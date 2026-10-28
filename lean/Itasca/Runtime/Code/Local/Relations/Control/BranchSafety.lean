import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessForward
import Itasca.Runtime.Code.Local.Callbacks.Calls.CallbackSafety
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem branch_underflow_total {A} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (frame : runtime.compiler.Frame)
    (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (underflow : compiler.height.val <
      (match frame.kind with | .Loop => frame.params | _ => frame.results).val) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ _ => True ⦄ := by
  cases kindEq : frame.kind
  all_goals simp only [kindEq] at underflow
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch
    step as ⟨last, lastValue⟩
    step as ⟨d, dValue⟩
    step as ⟨actualIndex, indexValue⟩
    have indexEq : actualIndex = index := by
      apply UScalar.eq_of_val_eq
      simp [alloc.vec.Vec.len] at lastValue
      scalar_tac
    subst actualIndex
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    step as ⟨found, foundValue⟩
    have foundEq : found = frame := foundValue.trans (List.getElem?_eq_some_iff.mp lookup).2
    rw [foundEq]
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false, ite_true]
    step as ⟨sum, sumValue⟩
    cases sum with
    | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | some sum =>
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step as ⟨source, sourceValue⟩
      cases source with
      | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | some source => simp at sumValue sourceValue; omega

@[step] theorem compiler_branch_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length + 2 ≤ Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length + 2 ≤ Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false ⦃ _ => True ⦄ := by
  by_cases loop : frame.kind = Itasca.code.LabelKind.Loop
  · by_cases enough : frame.params.val ≤ compiler.height.val
    · obtain ⟨source, _, sourceValue⟩ := WP.spec_imp_exists
        (UScalar.sub_spec (x := compiler.height) (y := frame.params) enough)
      apply WP.spec_mono (compiler_branch_loop ops law compiler frame index depth source
        lookup position loop (by omega) codeFits sourceFits coordinateFits)
      simp
    · exact branch_underflow_total ops compiler frame index depth lookup position (by simp [loop]; omega)
  · by_cases enough : frame.results.val ≤ compiler.height.val
    · obtain ⟨source, _, sourceValue⟩ := WP.spec_imp_exists
        (UScalar.sub_spec (x := compiler.height) (y := frame.results) enough)
      apply WP.spec_mono (compiler_branch_forward ops law compiler frame index depth source
        lookup position loop (by omega) fixupsFit codeFits sourceFits coordinateFits)
      simp
    · exact branch_underflow_total ops compiler frame index depth lookup position (by cases kindEq : frame.kind <;> simp_all)

end Itasca.Runtime.Code
