import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FrameSites
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSafety
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservation

/-!
END safety needs only retained fixup/map addresses and vector headroom, not a source body typing or final compilation-success hypothesis.

Main declarations: `compiler_end_total`. A direct consumer is `Compiler.Body.Relations.Control.ReachedControlSafety`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- END safety needs only retained fixup/map addresses and vector headroom,
not a source body typing or final compilation-success hypothesis. -/
@[step] theorem compiler_end_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (sites : FrameSites compiler.function.code.val frame)
    (bodyGuard : frame.kind = .Body → frame.if_pc = none)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (pcBound : compiler.function.code.val.length < 2^32)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have total : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
      ops compiler state .Block .Empty ⦃ _ => True ⦄ := by
    let target : U32 := UScalar.ofNatCore compiler.function.code.val.length pcBound
    by_cases body : frame.kind = .Body
    · exact WP.spec_mono (close_function_effect ops law compiler state frame rest target frames
        body (bodyGuard body) rfl sites.branches.branches mapFits coordinateFits codeFits sourceFits
        emitCoordinateFits) (by simp)
    · cases guardEq : frame.if_pc with
      | none =>
        exact WP.spec_mono (close_scope_effect ops law compiler state frame rest target frames body
          guardEq rfl sites.branches.branches mapFits coordinateFits) (by simp)
      | some guard =>
        obtain ⟨condition, old, found⟩ := sites.guard guard guardEq
        exact WP.spec_mono (close_guarded_scope_effect ops law compiler state frame rest target frames
          guard condition old body guardEq found rfl sites.branches.branches mapFits coordinateFits) (by simp)
  have same : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt =
      runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty := rfl
  rw [same]
  obtain ⟨⟨status, after⟩, call, _⟩ := WP.spec_imp_exists total
  rw [call, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := compiler_end_observation ops compiler after state .Block .Empty call
  have result := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at result
  exact result rfl

end Itasca.Runtime.Code
