import Exec.Code.Local.Callbacks.Table.CompilerTables
import Exec.Code.Local.Relations.Local.LocalDeclarations
import Exec.Code.Local.Callbacks.Control.EnterBlock
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- The successful function-start callback establishes the zero-operand layout,
source coordinates, and the root control frame used by all later callbacks. -/
@[step] theorem compiler_function_start_raw {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val + bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val + bodyEnd.val ≤ Usize.max)
    (emptyLocals : compiler.function.locals.val = [])
    (localLayout : LocalLayout compiler)
    (emptyOperands : compiler.before.val = [])
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
      out.1 = .Ok () → CompilerLayout out.2 [] ∧
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = compiler.frames.val ++
          [⟨0#usize, .Body, out.2.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        CompilerTables.ofFunction out.2.function = CompilerTables.ofFunction compiler.function ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
  step as ⟨start, startEq⟩
  step as ⟨finish, finishEq⟩
  step as ⟨index, indexEq⟩
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨sig, sigEq⟩
  have same : sig = signature := by simpa [indexEq, sigEq, List.getElem?_eq_getElem bound] using lookup
  rw [same]
  let initial := { compiler with function := { compiler.function with param_slots := signature.param_slots, type_index := typeIndex, body_start := start, body_end := finish } }
  have initialLayout : LocalLayout initial := ⟨localLayout.slots, localLayout.offsets⟩
  step with compiler_locals_loop ops law initial ctx 0#usize (by simp) initialLayout
    (by simpa [initial] using emptyLocals)
    as ⟨s, s1, b, i3, cf, v, b1, i4, v1, i5, v2, v3, result, updated, status, outputEq, certified⟩
  simp only [localLoopOutput, Prod.mk.injEq] at outputEq
  rcases outputEq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨frame, layout, types⟩ := certified rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_control ops updated.budget as ⟨status, budget⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have sameControls : updated.function.controls = compiler.function.controls := by rw [frame]
      have sameFrames : updated.frames = compiler.frames := by rw [frame]
      step with budget_push ops law budget updated.function.controls
        ⟨.Body, updated.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, signature.results⟩
        (by simpa [sameControls] using mapsFit) as ⟨status, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [bind_ok]
        step with budget_push ops law budget1 updated.frames
          ⟨0#usize, .Body, updated.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
          (by simpa [sameFrames] using framesFit) as ⟨status, budget2, frames, pushed⟩
        rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [bind_ok, WP.spec_ok]
          intro accepted
          refine ⟨⟨layout.slots, layout.offsets, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
          · have : updated.before = compiler.before := by rw [frame]
            simp [this, emptyOperands, stackOffsets]
          · simp only [compilerLocals, slots, Nat.add_zero]
            exact layout.slots
          · intro _; exact Nat.le_refl _
          · rw [frame]
          · simpa [sameFrames] using frameAppend
          · rw [frame]
            rfl
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Code
