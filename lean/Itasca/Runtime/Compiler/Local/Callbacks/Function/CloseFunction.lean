import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Lowering.Emission.Emit

/-!
Effects of closing the outermost compiled function.

Main declarations: `close_function_effect`. A direct consumer is `Compiler.Local.Callbacks.Control.CloseMapEffect`.
-/

namespace Itasca.Runtime.Compiler
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
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.total ops law compiler state .Block .Empty
    ⟨frame, rest, frames, branches, (by intro queried selected; rw [noIf] at selected; cases selected),
      mapFits, coordinateFits, (by intro body; exact ⟨codeFits, sourceFits, emitCoordinateFits⟩)⟩
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful ⊢
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops compiler after state .Block .Empty (.Ok ()) called
  obtain ⟨remaining, reachable, code, original, closed, selected, controls, start, sourceStart, endPc, sourceEnd⟩ :=
    effect.unguarded_success law frame rest target frames position noIf branches mapFits
  have closedLookup : after.function.controls.val[frame.map.val]? = some closed := by
    rw [controls]
    exact List.getElem?_set_self mapFits
  refine ⟨remaining, reachable, ?_, closed, closedLookup, endPc, sourceEnd⟩
  simpa only [kind, endReachable, scopeExitLive] using code

end Itasca.Runtime.Compiler
