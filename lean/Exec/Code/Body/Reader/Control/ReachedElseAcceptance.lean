import Exec.Code.Body.Reader.Acceptance.BodyReaderAcceptance
import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.ElseDispatchAvailability
import Exec.Code.Local.Callbacks.Common.FixupBudget
import Exec.Code.Body.Control.Table.StructuredPrefixDeadWithTables
import Exec.Code.Body.Reader.Common.ReaderCloseWasm1
import Exec.Code.Body.Reader.Common.ReaderCloseWasm2
import Exec.Code.Body.Reader.Control.ReaderScopeZipper

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- An independently selected then scope retains its unique unpatched guard.
Its frame shape and entry code justify all three actual else-entry paths. -/
theorem StructuredCompilerPrefixWithTables.else_available {A : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    {jumpTables emit initial compiler types functions returns locals parents current raw position}
    (invariant : @StructuredCompilerPrefixWithTables jumpTables emit A initial compiler types functions returns locals
      parents current raw position)
    (state : code.OpIterState) (capacity : CallbackCapacity compiler state bound 1)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (sourceBt : blocktype) (condition : U32) (form : current.form = .then_ sourceBt condition)
    (bt : signature.BlockType) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ result =>
      result.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget result.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
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
  have holes := fixups frame (by rw [frames]; simp)
  have room := capacity.codeCapacity
  have reserve := capacity.codeReserve
  simp only [alloc.vec.Vec.length] at room reserve
  exact compiler_else_available ops bound available compiler state capacity bt frame prior frames liveGuard owned
    (by change frame.fixups.val.length < Usize.max; omega)
    (by change frame.fixups.val.length+1 ≤ bound; omega)

/-- Independent source else acceptance identifies the active then-scope;
its physical guard and source-paid reserve establish actual compiler acceptance. -/
theorem reached_reader_else_available_wasm1 {jumpTables : List U32} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (capacity : CallbackCapacity compiler out bound 1)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_ELSE)
    (reference : code.step source st data env ctx code.OP_ELSE before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_ELSE compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,sourceForm,_⟩ := reader_else_wasm1 p source before after out byte reference
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Control.blockType p.current.ctrl.block_type) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  rw [OpDispatch.dispatch_else] at reference ⊢
  refine CoreVisitor.run.accepted_lift_on (code.read_else st)
    (fun v state bt => source.on_else v state (Control.signature bt))
    (fun v state bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_else v state
      (Control.signature bt)) before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  intro bt _ _
  exact invariant.else_available ops bound available out capacity fixups _ condition form (Control.signature bt)

/-- Independent source else acceptance identifies the active then-scope;
its physical guard and source-paid reserve establish actual compiler acceptance. -/
theorem reached_profile_else_available_wasm2 {jumpTables : List U32} {data env sourceLocals index st}
    (p : Wasm2.Pending data env sourceLocals index st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.BodyState) (ctx : code.Context)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (capacity : CallbackCapacity compiler out.core bound 1)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (byte : data.val[p.start.val]'p.inbounds = 5#u8)
    (reference : code.step_profile source st data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
    code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 5#u8 compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  obtain ⟨_,_,sourceForm,_⟩ := reader_else_wasm2 p source before after out ctx byte reference
  have matched := same.current.form
  rw [sourceForm] at matched
  have sourceThen : ∃ condition, current.form = .then_ (Wasm2.blockType p.current.bt) condition := by
    generalize currentForm : current.form = scopeForm at matched
    cases matched with
    | then_ condition => exact ⟨condition,rfl⟩
  obtain ⟨condition,form⟩ := sourceThen
  rw [Wasm2.CallbackTrace.dispatch_else] at reference ⊢
  refine Wasm2.CallbackTrace.bodyRun.accepted_lift_on _ source
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) _ before after compiler out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions then 1 else 0)) reference ?_
  rintro ⟨kind,bt⟩ _ _
  exact invariant.else_available ops bound available out.core capacity fixups _ condition form bt

end Exec.Code
