import Itasca.Runtime.Compiler.Body.Control.Table.StructuredPrefixDead
import Itasca.Runtime.Compiler.Local.Checking.ScopeCloseInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2

/-!
Structured compiler scope-close checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Close Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
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

end Itasca.Runtime.Compiler

end

/-! ## Reader End Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- The actual Wasm 2 END reader supplies progress and a bounded source
endpoint for nested scope instruction checking. -/
theorem reader_nested_end_open_instructions_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env .Wasm2 localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (nonRoot : current.form ≠ .body)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (byte : data.val[p.start.val]'p.inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) st data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨callback,_,_,_,_,afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := afterState.2.1
    omega
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    omega
  exact structured_scope_close_open_instructions ops law invariant sourceBound out.core p.current.ctrl.kind
    p.current.bt nonRoot maps held consumed endBound callback

end Itasca.Runtime.Compiler

end
