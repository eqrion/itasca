import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit

/-!
Effects of closing the outermost compiled function.

Main declarations: `close_function_effect`. A direct consumer is `Compiler.Local.Callbacks.Control.CloseMapEffect`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std
@[step] theorem close_function_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = scopeExitLive compiler.reachable frame ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
          [.Return frame.height (if scopeExitLive compiler.reachable frame then frame.results else 0#u32)] ∧
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
  have choice : (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) = .ok (frame.kind, scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases reach : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive, kind, reach, ends, bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) _) _
  rw [choice, bind_ok]
  simp only [kind, bind_ok]
  change WP.spec (Aeneas.Std.bind (.ok true) _) _
  rw [bind_ok]
  simp only [ite_true]
  have codeLength : code.val.length = compiler.function.code.val.length := by
    simpa only [patchCode_length] using congrArg List.length effect
  change WP.spec (Aeneas.Std.bind (if scopeExitLive compiler.reachable frame then
    .ok frame.results else .ok 0#u32) _) _
  have choose : (if scopeExitLive compiler.reachable frame then .ok frame.results else .ok 0#u32) =
      (.ok (if scopeExitLive compiler.reachable frame then frame.results else 0#u32) : Result U32) := by split <;> rfl
  rw [choose, bind_ok]
  let updated := { compiler with frames := rest, reachable := scopeExitLive compiler.reachable frame, function := { compiler.function with code, controls := back { map with source_end := coordinate, end_pc := pcword } } }
  step with compiler_emit ops law updated _ (by simpa [updated, codeLength] using codeFits)
    (by simpa [updated] using sourceFits) (by simpa [updated] using emitCoordinateFits) as
    ⟨status, emitted, hEmitted⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    have emittedEffect := hEmitted rfl
    obtain ⟨budget, instructions, sources, rfl, emittedCode, emittedSources⟩ := emittedEffect
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_observe ops law _ state as ⟨out, hout, success⟩
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := hout success
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hframes
    · simpa using hr
    · rw [hcode]
      simpa only [effect, List.drop_zero] using emittedCode
    · refine ⟨{ map with source_end := coordinate, end_pc := pcword }, ?_, ?_, hcoordinate⟩
      · rw [hcontrols, hback]
        simp [alloc.vec.Vec.set_val_eq, mapFits]
      · rw [hpcword]
        scalar_tac


end Itasca.Runtime.Code
