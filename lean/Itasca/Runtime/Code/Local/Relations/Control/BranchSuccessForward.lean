import Itasca.Runtime.Code.Local.Relations.Control.BranchSuccessEmit
import Itasca.Runtime.Code.Local.Lowering.Control.LoweringForwardBranch
import Itasca.Runtime.Code.Local.Lowering.Control.LoweringLoopBranch
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
theorem branch_index {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length) :
    (do
      let last ← alloc.vec.Vec.len compiler.frames - 1#usize
      let d ← lift (UScalar.cast .Usize depth)
      let selected ← last - d
      let found ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame) compiler.frames selected
      Result.ok (selected, found)) ⦃ out => out = (index, frame) ⦄ := by
  step as ⟨last, hlast⟩
  step as ⟨d, hd⟩
  step as ⟨actualIndex, hindex⟩
  have indexEq : actualIndex = index := by apply UScalar.eq_of_val_eq; simp [alloc.vec.Vec.len] at hlast; scalar_tac
  subst actualIndex
  have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [List.getElem?_eq_getElem inBounds, hfound] using lookup
  simp [foundEq]

theorem branch_transfer_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (nonempty : frame.results ≠ 0#u32)
    (different : source ≠ frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [transferInstruction frame.height source frame.results, .Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length + 1 ∧
          after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] := by
  cases kindEq : frame.kind
  all_goals try exact (forward kindEq).elim
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch at accepted
    obtain ⟨last, hlast, rest⟩ := bind_ok_inv _ _ _ accepted
    clear accepted
    obtain ⟨d, hd, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨actualIndex, hindex, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨found, hfound, rest⟩ := bind_ok_inv _ _ _ rest
    have indexSpec := branch_index compiler frame index depth lookup position
    simp only [hlast, hd, hindex, hfound, bind_ok, WP.spec_ok] at indexSpec
    have indexEq := (Prod.mk.inj indexSpec).1
    have foundEq := (Prod.mk.inj indexSpec).2
    subst actualIndex found
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false] at rest
    have sumSpec : lift (U32.checked_add 0#u32 frame.results) ⦃ out => out = some frame.results ⦄ := by
      step as ⟨sum, hsum⟩
      cases sum with
      | none => simp at hsum; scalar_tac
      | some sum => congr 1; apply UScalar.eq_of_val_eq; simpa using hsum.2.1
    obtain ⟨_, sumCall, rfl⟩ := WP.spec_imp_exists sumSpec
    rw [sumCall] at rest
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have sourceSpec : lift (U32.checked_sub compiler.height frame.results) ⦃ out => out = some source ⦄ := by
      step as ⟨operand, hoperand⟩
      cases operand with
      | none => simp at hoperand; scalar_tac
      | some operand => congr 1; apply UScalar.eq_of_val_eq; simp at hoperand; omega
    obtain ⟨_, sourceCall, rfl⟩ := WP.spec_imp_exists sourceSpec
    rw [sourceCall] at rest
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Bool.false_eq_true, ite_false] at rest
    simp only [bne_iff_ne, if_pos nonempty, bind_ok, if_pos different] at rest
    obtain ⟨⟨copied, afterCopy⟩, copiedCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases copied with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      obtain ⟨copyBudget, copyCode, copyOffsets, rfl, copiedCode, copiedOffsets⟩ :=
        compiler_copy_success ops law compiler afterCopy frame.height source frame.results nonempty different copiedCall
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨current, back⟩, read, rest⟩ := bind_ok_inv _ _ _ rest
      have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
          compiler.frames index ⦃ out => out.1 = frame ∧ ∀ replacement, (out.2 replacement).val = compiler.frames.val.set index.val replacement ⦄ := by
        step as ⟨out, hcurrent, hback⟩
        have same : out.1 = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
        exact ⟨same, by intro replacement; simp [hback, alloc.vec.Vec.set_val_eq]⟩
      rw [read, WP.spec_ok] at readSpec
      have currentEq := readSpec.1
      have hback := readSpec.2
      dsimp only at currentEq hback
      subst current
      simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false] at rest
      obtain ⟨⟨pushed, budget, fixups⟩, pushedCall, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        cases value
        have appended := (budget_push_success ops law copyBudget budget frame.fixups fixups (alloc.vec.Vec.len copyCode) pushedCall).2
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
          Bool.false_eq_true, ite_false] at rest
        obtain ⟨⟨result, afterJump⟩, emittedCall, rest⟩ := bind_ok_inv _ _ _ rest
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
        | Ok value =>
          cases value
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Bool.false_eq_true, ite_false, Result.ok.injEq, Prod.mk.injEq] at rest
          obtain ⟨_, rfl⟩ := rest
          have emitted := compiler_emit_success ops law _ afterJump (.Jump core.num.U32.MAX) emittedCall
          obtain ⟨finalBudget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted
          refine ⟨?_, fixups, alloc.vec.Vec.len copyCode, ?_, ?_, appended⟩
          · simpa [exactState, copiedCode, List.append_assoc] using finalCode
          · simp [alloc.vec.Vec.len, copiedCode]
          · simp [exactState, hback, kindEq]

theorem branch_elided_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop) (elided : frame.results = 0#u32 ∨ source = frame.height)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          [.Jump core.num.U32.MAX] ∧
        ∃ fixups site, site.val = compiler.function.code.val.length ∧
          after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
          fixups.val = frame.fixups.val ++ [site] := by
  cases kindEq : frame.kind
  all_goals try exact (forward kindEq).elim
  all_goals
    unfold runtime.compiler.control.FunctionCompiler.branch at accepted
    obtain ⟨last, hlast, rest⟩ := bind_ok_inv _ _ _ accepted
    clear accepted
    obtain ⟨d, hd, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨actualIndex, hindex, rest⟩ := bind_ok_inv _ _ _ rest
    obtain ⟨found, hfound, rest⟩ := bind_ok_inv _ _ _ rest
    have indexSpec := branch_index compiler frame index depth lookup position
    simp only [hlast, hd, hindex, hfound, bind_ok, WP.spec_ok] at indexSpec
    have indexEq := (Prod.mk.inj indexSpec).1
    have foundEq := (Prod.mk.inj indexSpec).2
    subst actualIndex found
    have inBounds := (List.getElem?_eq_some_iff.mp lookup).1
    simp only [kindEq, bind_ok, Bool.false_eq_true, ite_false] at rest
    have sumSpec : lift (U32.checked_add 0#u32 frame.results) ⦃ out => out = some frame.results ⦄ := by
      step as ⟨sum, hsum⟩
      cases sum with
      | none => simp at hsum; scalar_tac
      | some sum => congr 1; apply UScalar.eq_of_val_eq; simpa using hsum.2.1
    obtain ⟨_, sumCall, rfl⟩ := WP.spec_imp_exists sumSpec
    rw [sumCall] at rest
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have sourceSpec : lift (U32.checked_sub compiler.height frame.results) ⦃ out => out = some source ⦄ := by
      step as ⟨operand, hoperand⟩
      cases operand with
      | none => simp at hoperand; scalar_tac
      | some operand => congr 1; apply UScalar.eq_of_val_eq; simp at hoperand; omega
    obtain ⟨_, sourceCall, rfl⟩ := WP.spec_imp_exists sourceSpec
    rw [sourceCall] at rest
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Bool.false_eq_true, ite_false] at rest
    have copyFalse : (if frame.results != 0#u32 then (Result.ok (source != frame.height) : Result Bool)
        else Result.ok false) = Result.ok false := by rcases elided with h | h <;> simp [h]
    rw [copyFalse] at rest
    simp only [bind_ok, Bool.false_eq_true, ite_false] at rest
    obtain ⟨⟨current, back⟩, read, rest⟩ := bind_ok_inv _ _ _ rest
    have readSpec : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice runtime.compiler.Frame)
        compiler.frames index ⦃ out => out.1 = frame ∧ ∀ replacement, (out.2 replacement).val = compiler.frames.val.set index.val replacement ⦄ := by
      step as ⟨out, hcurrent, hback⟩
      have same : out.1 = frame := by simpa [List.getElem?_eq_getElem inBounds, hcurrent] using lookup
      exact ⟨same, by intro replacement; simp [hback, alloc.vec.Vec.set_val_eq]⟩
    rw [read, WP.spec_ok] at readSpec
    have currentEq := readSpec.1
    have hback := readSpec.2
    dsimp only at currentEq hback
    subst current
    simp only [kindEq, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false] at rest
    obtain ⟨⟨pushed, budget, fixups⟩, pushedCall, rest⟩ := bind_ok_inv _ _ _ rest
    cases pushed with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
    | Ok value =>
      cases value
      have appended := (budget_push_success ops law compiler.budget budget frame.fixups fixups (alloc.vec.Vec.len compiler.function.code) pushedCall).2
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
        Bool.false_eq_true, ite_false] at rest
      obtain ⟨⟨result, afterJump⟩, emittedCall, rest⟩ := bind_ok_inv _ _ _ rest
      cases result with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
      | Ok value =>
        cases value
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, Bool.false_eq_true, ite_false, Result.ok.injEq, Prod.mk.injEq] at rest
        obtain ⟨_, rfl⟩ := rest
        have emitted := compiler_emit_success ops law _ afterJump (.Jump core.num.U32.MAX) emittedCall
        obtain ⟨finalBudget, code, offsets, exactState, finalCode, finalOffsets⟩ := emitted
        refine ⟨?_, fixups, alloc.vec.Vec.len compiler.function.code, ?_, ?_, appended⟩
        · simpa [exactState] using finalCode
        · simp [alloc.vec.Vec.len]
        · simp [exactState, hback, kindEq]
end Itasca.Runtime.Code
