import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Checking.ElseExitSlotBounds
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeZipper
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Stacks.Stacks

/-!
Structured compiler else exit slots and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Else Exit Slots -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Source THEN geometry provides the owned guard needed by actual ELSE in
live, terminated, and unentered arms. -/
theorem StructuredCompilerPrefix.else_exit_slots {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {jumpTables emit initial compiler after types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefix jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (sourceBt : blocktype) (condition : U32)
    (form : current.form = .then_ sourceBt condition) (bt : signature.BlockType)
    (normalStack : compiler.reachable = true → Sequence.stackTypes raw = current.front++current.results)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (held : FrameExitSlotBounds compiler)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
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
  apply compiler_else_exit_slots ops law compiler after state bt frame prior frames owned ?_ ?_ ?_ held called
  · intro absent
    by_cases live : compiler.reachable = true
    · exact False.elim (liveGuard live absent)
    · cases reachable : compiler.reachable <;> simp_all
  · intro live
    obtain ⟨entered,retained⟩ := invariant.live live
    have region := retained.layout.live_slots_fit live
    have height := shape.height entered
    have width := shape.results
    rw [normalStack live,retained.localsEq,slots_append] at region
    omega
  · have room := invariant.codeBudget
    unfold SourceCodeBudget at room
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    scalar_tac

end Itasca.Runtime.Code

end

/-! ## Reader Else Exit Slots -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- Actual ELSE reading preserves stored instruction checks from its matched THEN scope. -/
theorem reader_else_exit_slots_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env .Wasm2 sourceLocals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (monomorphic : before.reachable = true → p.current.ctrl.polymorphic_base = false)
    (held : FrameExitSlotBounds before)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) : FrameExitSlotBounds after := by
  obtain ⟨callback,read,sourceForm,encoded,results,opened,afterState⟩ := reader_else_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  obtain ⟨C,outer,spine,header,base,typed,ctrls,blocks,vals⟩ := p.opened
  have frontEq : current.front = Sequence.stackTypes outer := by
    rw [wasm2_spine_values spine]
    simpa only [List.flatMap_def] using fronts.current
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = current.front ++ current.results := by
    intro live
    have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ invariant.known live)).2
    have mono := monomorphic live
    have realized := results
    rw [mono] at realized
    have segmentTypes := (realized_concrete_types segmentKnown realized).symm
    simp only [vals, Sequence.stackTypes, List.map_append]
    change Sequence.stackTypes outer ++ Sequence.stackTypes p.current.vals = _
    rw [segmentTypes, ← frontEq, same.current.results]
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  exact invariant.else_exit_slots ops law out.core _ condition form p.current.bt stack sourceBound held callback

end Itasca.Runtime.Code

end
