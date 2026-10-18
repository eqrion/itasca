import Exec.Code.Local.Callbacks.Common.Fixups
import Exec.Code.Local.Callbacks.Common.Observe
/-! Closing a reachable ordinary block removes its compiler frame, resolves
its complete forward-fixup list, records the source/bytecode exit coordinates,
and preserves reachability. The proof follows the actual extracted callback. -/

namespace Exec.Code
open Aeneas Aeneas.Std

theorem compiler_pc_eq {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (target : U32)
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.pc ops compiler = .ok (.Ok target, compiler) := by
  unfold runtime.compiler.FunctionCompiler.pc
  simp only [lift, bind_ok]
  split
  · rename_i tooLarge
    have bound := target.hmax
    simp only [alloc.vec.Vec.len, core.num.U32.MAX, U32.rMax] at tooLarge
    scalar_tac
  · congr 3
    apply UScalar.eq_of_val_eq
    simp only [UScalar.cast_val_eq, alloc.vec.Vec.len]
    scalar_tac
@[step] theorem close_block_join {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Block) (noIf : frame.if_pc = none)
    (reachable : compiler.reachable = true ∨ frame.end_reachable = true)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = true ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ∧
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
  change WP.spec (Aeneas.Std.bind (.ok false) _) _
  rw [bind_ok]
  simp only [Bool.false_eq_true, ite_false]
  step with compiler_observe ops law _ state as ⟨out, hout, success⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := hout success
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hframes
  · simpa using hr
  · simpa [hcode] using effect
  · refine ⟨{ map with source_end := coordinate, end_pc := pcword }, ?_, ?_, hcoordinate⟩
    · rw [hcontrols, hback]
      simp [alloc.vec.Vec.set_val_eq, mapFits]
    · rw [hpcword]
      scalar_tac

@[step] theorem close_block {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Block) (noIf : frame.if_pc = none)
    (reachable : compiler.reachable = true)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = true ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ∧
        ∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val ⦄ := by
  exact close_block_join ops law compiler state frame rest target frames kind noIf
    (Or.inl reachable) position branches mapFits coordinateFits

end Exec.Code
