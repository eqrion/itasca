import Exec.Code.Local.Callbacks.Control.CloseBlock
import Exec.Code.Local.Lowering.Common.Emit
/-! Closing the function body resolves its label fixups, records the final
source/bytecode coordinates, and emits the exact implicit Return epilogue. -/

namespace Exec.Code
open Aeneas Aeneas.Std

@[step] theorem close_body {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (reachable : compiler.reachable = true ∨ frame.end_reachable = true)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Body .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = true ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
          [.Return frame.height frame.results] ∧
        ∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, noIf]
  step with compiler_fixups ops { compiler with frames := rest } frame.fixups target 0#usize
    (by simp) branches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  have choice {T : Type} (yes no : T) :
      (if compiler.reachable then yes else if frame.end_reachable then yes else no) = yes := by
    rcases reachable with live | reached
    · simp [live]
    · simp [reached]
  simp only [choice, kind, bind_ok]
  simp only [uncurry_apply_pair, bind_ok, ite_true]
  have patchedFits : code.val.length < Usize.max := by
    rw [effect, List.drop_zero, patchCode_length]
    exact codeFits
  step with compiler_emit ops law
    { compiler with frames := rest, reachable := true, function := { compiler.function with code, controls := back { map with source_end := coordinate, end_pc := pcword } } }
    (.Return frame.height frame.results) patchedFits sourceFits emitCoordinateFits
    as ⟨result, emitted, emission⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨budget, finalCode, sources, exactState, appended, sourceAppended⟩ := emission rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law emitted state as ⟨out, hout, success⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := hout success
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [exactState] using hframes
    · simpa [exactState] using hr
    · rw [hcode, exactState]
      dsimp only
      rw [appended, effect]
      simp
    · refine ⟨{ map with source_end := coordinate, end_pc := pcword }, ?_, ?_, hcoordinate⟩
      · rw [hcontrols, exactState]
        dsimp only
        rw [hback]
        simp [alloc.vec.Vec.set_val_eq, mapFits]
      · rw [hpcword]
        scalar_tac
end Exec.Code
