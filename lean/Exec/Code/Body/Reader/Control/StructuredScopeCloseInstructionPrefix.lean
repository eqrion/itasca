import Exec.Code.Body.Control.Table.StructuredPrefixDead
import Exec.Code.Local.Checking.ScopeCloseInstructionPrefix

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source scope metadata and retained branch sites preserve instruction
checking through actual nested END, including guard patching. -/
theorem structured_scope_close_open_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have priorBound : prior.length ≤ Usize.max := by
    have bound := before.frames.property
    simp only [frames,List.length_append,List.length_singleton] at bound
    omega
  let rest := alloc.vec.Vec.from prior priorBound
  have restVal : rest.val = prior := by simp [rest]
  have fetchBound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := invariant.mode.sites frame (by simp [frames])
  let geometry : ScopeCloseGeometry before :=
    ⟨frame,rest,target,by simpa only [restVal] using frames,rfl,sites.branches.branches⟩
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by omega
  have nonBody : frame.kind ≠ .Body := by
    have kind := shape.kind
    cases form : current.form <;> simp_all [ScopeForm.kind]
  have coordinateFits : before.function.body_start.val+state.pos.val ≤ Usize.max := by
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    omega
  apply compiler_scope_close_open_instructions ops law before after state kind bt geometry _ nonBody maps coordinateFits held called
  cases hasIf : frame.if_pc with
  | none =>
    obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
    have bound : before.function.body_end.val ≤ Usize.max := by scalar_tac
    have emitFits : before.function.body_start.val+before.next_source.val ≤ Usize.max := by omega
    exact .unguarded hasIf codeFits offsetsFit emitFits
  | some guard =>
    obtain ⟨condition,old,guardCode⟩ := sites.guard guard hasIf
    have nonBody : frame.kind ≠ .Body := by
      intro root
      have body : current.form = .body := by
        have same := shape.kind.symm.trans root
        cases form : current.form <;> simp_all [ScopeForm.kind]
      have guardPosition := shape.guard
      simp only [body,SourceScope.guardPosition,hasIf,Option.map_some] at guardPosition
      cases guardPosition
    exact .guarded guard condition old nonBody hasIf guardCode

end Itasca.Runtime.Code
