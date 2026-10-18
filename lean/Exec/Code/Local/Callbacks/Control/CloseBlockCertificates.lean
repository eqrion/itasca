import Exec.Code.Local.Relations.Control.BranchCertificates
import Exec.Code.Local.Callbacks.Control.CloseBlock
namespace Exec.Code
open Aeneas Aeneas.Std

/-- The source END callback resolves the retained source branches of its label,
not merely isolated numeric patch addresses. -/
@[step] theorem close_block_join_certificates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (types functions : List functype) (returns locals final : List valtype)
    (labels : List LabelTarget) (pending : List PendingBranch)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Block) (noIf : frame.if_pc = none)
    (reachable : compiler.reachable = true ∨ frame.end_reachable = true)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (invariant : OpenBranches locals compiler.function.code.val labels target frame.fixups.val pending)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = true ∧
        (∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val) ∧
        ∀ branch, branch ∈ pending →
          CodeRel types functions returns locals out.2.function.code.val labels branch.stack
            (.BR (.mk_uN branch.depth) :: branch.sourceTail) branch.pc
            (branch.pc + (branchInstructions branch.dst branch.src branch.count target).length) final ⦄ := by
  apply WP.spec_mono (close_block_join ops law compiler state frame rest target frames kind noIf reachable
    position branches mapFits coordinateFits)
  intro out success accepted
  obtain ⟨popped, live, effect, control⟩ := success accepted
  refine ⟨popped, live, control, ?_⟩
  intro branch member
  obtain ⟨label, lookup, live, sameTarget, layout, hole⟩ := invariant branch member
  have resolved := hole.resolve target
  apply CodeRel.branch lookup live layout (by simpa [effect, sameTarget] using resolved) (Nat.le_refl _)
  simpa [effect] using resolved.next_bound
@[step] theorem close_block_certificates {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (types functions : List functype) (returns locals final : List valtype)
    (labels : List LabelTarget) (pending : List PendingBranch)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Block) (noIf : frame.if_pc = none)
    (reachable : compiler.reachable = true)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (invariant : OpenBranches locals compiler.function.code.val labels target frame.fixups.val pending)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () →
        out.2.frames = rest ∧ out.2.reachable = true ∧
        (∃ closed, out.2.function.controls.val[frame.map.val]? = some closed ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val + state.pos.val) ∧
        ∀ branch, branch ∈ pending →
          CodeRel types functions returns locals out.2.function.code.val labels branch.stack
            (.BR (.mk_uN branch.depth) :: branch.sourceTail) branch.pc
            (branch.pc + (branchInstructions branch.dst branch.src branch.count target).length) final ⦄ := by
  exact close_block_join_certificates ops law compiler state frame rest target types functions returns locals final
    labels pending frames kind noIf (Or.inl reachable) position branches invariant mapFits coordinateFits

end Exec.Code
