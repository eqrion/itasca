import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Checking.ElseCallbackInstructionPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeZipper

/-!
Structured compiler else checked instruction prefixes and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Else Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source THEN geometry provides the owned guard needed by actual ELSE in
live, terminated, and unentered arms. -/
theorem StructuredCompilerPrefix.else_open_instructions {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {jumpTables emit initial compiler after types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (sourceBt : blocktype) (condition : U32)
    (form : current.form = .then_ sourceBt condition) (bt : signature.BlockType)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (held : CompilerInstructionPrefix compiler)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (),after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨prior,frame,frames,_,shape⟩ := invariant.frames.split
  have liveGuard : compiler.reachable = true → frame.if_pc ≠ none := by
    intro live absent
    have entered := (invariant.live live).1
    have guard := shape.guard
    simp [absent,form,SourceScope.guardPosition,entered] at guard
  have owned : ∀ guard, frame.if_pc = some guard → ∃ operand,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero operand core.num.U32.MAX) := by
    intro guard selected
    have same := shape.guard
    simp only [selected,Option.map_some,form,SourceScope.guardPosition] at same
    cases entered : current.entered with
    | false => simp [entered] at same
    | true =>
      have position : guard.val = current.entry := by simpa [entered] using same
      refine ⟨condition,?_⟩
      rw [position]
      have entry : current.entered = true → compiler.function.code.val[current.entry]? =
          some (.JumpIfZero condition core.num.U32.MAX) := by
        simpa [ScopeEntryCode,form] using shape.entryCode
      exact entry entered
  apply compiler_else_open_instructions ops law compiler after state bt frame prior frames owned ?_ ?_ held called
  · intro absent
    by_cases live : compiler.reachable = true
    · exact False.elim (liveGuard live absent)
    · cases reachable : compiler.reachable <;> simp_all
  · have room := invariant.codeBudget
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac

end Itasca.Runtime.Compiler

end

/-! ## Reader Else Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_open_instructions_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (held : CompilerInstructionPrefix before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) : CompilerInstructionPrefix after := by
  obtain ⟨callback,_,sourceForm,_⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_open_instructions ops law out.core _ condition form p.current.bt sourceBound held callback

end Itasca.Runtime.Compiler

end
