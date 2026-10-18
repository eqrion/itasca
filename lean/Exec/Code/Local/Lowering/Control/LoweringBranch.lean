import Exec.Code.Local.Relations.Control.BranchCertificates
import Exec.Code.Local.Initializer.InitializerExpression
import Exec.Code.Local.Callbacks.Common.Observe
/-! Actual zero-result forward branches construct retained fixup holes and
mark the source continuation unreachable; END resolves those holes. -/

namespace Exec.Code
open Aeneas Aeneas.Std

set_option maxRecDepth 4096 in
@[step] theorem branch_zero_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (rest : List runtime.compiler.Frame)
    (frames : compiler.frames.val = rest ++ [frame])
    (kind : frame.kind = .Block) (arity : frame.results = 0#u32)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.control.FunctionCompiler.branch ops compiler 0#u32 0#u32 false ⦃ out =>
      out.1 = .Ok () →
        out.2.function.code.val = compiler.function.code.val ++ [.Jump 4294967295#u32] ∧
        ∃ fixups, out.2.frames.val = rest ++ [{ frame with end_reachable := true, fixups }] ∧
          fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ⦄ := by
  unfold runtime.compiler.control.FunctionCompiler.branch
  step as ⟨last, hlast⟩
  step as ⟨zero, hzero⟩
  step as ⟨index, hindex⟩
  have indexAt : index.val = rest.length := by simp [frames, alloc.vec.Vec.len] at hlast; scalar_tac
  have inBounds : index.val < compiler.frames.length := by simp [indexAt, frames, alloc.vec.Vec.length]
  step as ⟨found, hfound⟩
  have foundEq : found = frame := by simpa [indexAt, frames] using hfound
  rw [foundEq]
  simp only [kind, bind_ok, Bool.false_eq_true, ite_false, arity]
  step as ⟨sum, hsum⟩
  cases sum with
  | none => simp at hsum
  | some sum =>
    have sumZero : sum = 0#u32 := by
      apply UScalar.eq_of_val_eq
      change sum.val = 0
      simpa only [Nat.zero_add] using hsum.2.1
    rw [sumZero]
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step as ⟨source, hsource⟩
    cases source with
    | none => simp at hsource
    | some source =>
      have same : source = compiler.height := by apply UScalar.eq_of_val_eq; simp at hsource; omega
      rw [same]
      simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        bind_ok, Bool.false_eq_true, ite_false, bne_self_eq_false]
      step as ⟨current, back, hcurrent, hback⟩
      have currentEq : current = frame := by simpa [indexAt, frames] using hcurrent
      rw [currentEq]
      simp only [kind, bind_ok, uncurry_apply_pair, Bool.false_eq_true, ite_false]
      step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code) fixupsFit
        as ⟨result, budget, fixups, hpush⟩
      rcases hpush with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair,
          Bool.false_eq_true, ite_false]
        step with compiler_emit ops law
          { compiler with frames := back { frame with kind := .Block, end_reachable := true, fixups } }
          (.Jump core.num.U32.MAX) codeFits sourceFits coordinateFits
          as ⟨result, output, emitted⟩
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok value =>
          cases value
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          simp only [WP.spec_ok]
          intro accepted
          obtain ⟨b, code, sources, exactState, codeAppended, sourceAppended⟩ := emitted rfl
          refine ⟨?_, ?_⟩
          · simpa [exactState, core.num.U32.MAX, U32.rMax] using codeAppended
          · refine ⟨fixups, ?_, appended⟩
            simp [exactState, hback, alloc.vec.Vec.set_val_eq, frames, indexAt, kind, arity]
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem callback_branch_zero_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (frame : runtime.compiler.Frame) (rest : List runtime.compiler.Frame)
    (frames : compiler.frames.val = rest ++ [frame])
    (kind : frame.kind = .Block) (arity : frame.results = 0#u32)
    (reachable : compiler.reachable = true)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state 0#u32 resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        out.2.function.code.val = compiler.function.code.val ++ [.Jump 4294967295#u32] ∧
        ∃ fixups, out.2.frames.val = rest ++ [{ frame with end_reachable := true, fixups }] ∧
          fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
  rw [if_pos reachable]
  step with branch_zero_block ops law compiler frame rest frames kind arity fixupsFit
    codeFits sourceFits coordinateFits as ⟨result, changed, effect⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨code, fixups, frames', appended⟩ := effect rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law { changed with reachable := false } state as ⟨out, observed, accepted⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
    exact ⟨hr, by simpa [hcode] using code, fixups, by simpa [hframes] using frames', appended⟩

/-- Actual BR callback success supplies the forward placeholder certificate
consumed by the block END proof, including its newly recorded fixup address. -/
@[step] theorem callback_branch_zero_hole {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (frame : runtime.compiler.Frame) (rest : List runtime.compiler.Frame)
    (frames : compiler.frames.val = rest ++ [frame])
    (kind : frame.kind = .Block) (arity : frame.results = 0#u32)
    (reachable : compiler.reachable = true)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state 0#u32 resultType ⦃ out =>
      out.1 = .Ok () → out.2.reachable = false ∧
        ∃ fixups, out.2.frames.val = rest ++ [{ frame with end_reachable := true, fixups }] ∧
          BranchHole out.2.function.code.val fixups.val compiler.function.code.val.length
            frame.height compiler.height 0#u32 ⦄ := by
  apply WP.spec_mono (callback_branch_zero_block ops law compiler state resultType frame rest frames
    kind arity reachable fixupsFit codeFits sourceFits coordinateFits)
  intro out result accepted
  obtain ⟨dead, code, fixups, frames', appended⟩ := result accepted
  refine ⟨dead, fixups, frames', ?_⟩
  simp only [BranchHole, true_or, if_true]
  refine ⟨alloc.vec.Vec.len compiler.function.code, ?_, rfl, ?_⟩
  · simp [appended]
  · simp [code]
end Exec.Code
