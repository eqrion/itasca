import Exec.Code.Body.Reader.Common.ReaderEnterWasm1
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Local.Capacity.ReaderAcceptance
import Exec.Code.Local.Capacity.ScopeAvailability
import Exec.Code.Body.Control.Table.StructuredCompilerPrefixWithTables

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace
set_option maxRecDepth 4096

/-- Source-validated Wasm 1 block entry supplies its actual frame and
signature before the compiler runs. All resource obligations are numeric. -/
theorem reached_reader_block_available_wasm1 {jumpTables : List U32} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out bound) (scope : ScopeDemand compiler out bound)
    (pcRoom : compiler.function.code.length+1 ≤ U32.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_BLOCK)
    (reference : code.step source st data env ctx code.OP_BLOCK before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_BLOCK compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  obtain ⟨bt,_,read,post⟩ := reader_block_wasm1 p source before after out byte reference
  obtain ⟨signature,selected,_⟩ := wasm1_signature_select compiler.signatures bt
  have conditionLayout : compiler.reachable = true → code.LabelKind.Block = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32]) := by
    intro _ impossible
    cases impossible
  have callback := compiler_enter_available ops bound available compiler out demand scope
    (Wasm1.Frames.Saved.fresh out .block bt).ctrl
    ((p.parents ++ [{p.current with vals := p.current.vals}]).map Wasm1.Frames.Saved.ctrl)
    .Block (Control.signature bt) signature post.front.1 selected
    (by simp [Wasm1.Frames.Saved.fresh,Control.frame,alloc.vec.Vec.len]) pcRoom conditionLayout
  rw [OpDispatch.dispatch_block]
  exact CoreVisitor.run.available_of_read (code.read_block st data)
    (fun v state bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_block
      v state (Control.signature bt)) compiler bt out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)) read callback

/-- Source-validated Wasm 1 loop entry supplies its actual frame and
signature before the compiler runs. All resource obligations are numeric. -/
theorem reached_reader_loop_available_wasm1 {jumpTables : List U32} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out bound) (scope : ScopeDemand compiler out bound)
    (pcRoom : compiler.function.code.length+1 ≤ U32.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_LOOP)
    (reference : code.step source st data env ctx code.OP_LOOP before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_LOOP compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  obtain ⟨bt,_,read,post⟩ := reader_loop_wasm1 p source before after out byte reference
  obtain ⟨signature,selected,_⟩ := wasm1_signature_select compiler.signatures bt
  have conditionLayout : compiler.reachable = true → code.LabelKind.Loop = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32]) := by
    intro _ impossible
    cases impossible
  have callback := compiler_enter_available ops bound available compiler out demand scope
    (Wasm1.Frames.Saved.fresh out .loop bt).ctrl
    ((p.parents ++ [{p.current with vals := p.current.vals}]).map Wasm1.Frames.Saved.ctrl)
    .Loop (Control.signature bt) signature post.front.1 selected
    (by simp [Wasm1.Frames.Saved.fresh,Control.frame,alloc.vec.Vec.len]) pcRoom conditionLayout
  rw [OpDispatch.dispatch_loop]
  exact CoreVisitor.run.available_of_read (code.read_loop st data)
    (fun v state bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_loop
      v state (Control.signature bt)) compiler bt out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)) read callback

/-- Source-validated Wasm 1 if entry supplies its actual frame and
signature before the compiler runs. All resource obligations are numeric. -/
theorem reached_reader_if_available_wasm1 {jumpTables : List U32} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A V : Type}
    (ops : runtime.platform.Alloc A) (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (initial compiler : runtime.compiler.FunctionCompiler A)
    (source : code.OpVisitor V) (before after : V) (out : code.OpIterState)
    {emit types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial compiler
      types functions returns locals parents current st.vals.val p.start.val)
    (monomorphic : compiler.reachable = true → p.current.ctrl.polymorphic_base = false)
    (demand : CallbackDemand compiler out bound) (scope : ScopeDemand compiler out bound)
    (pcRoom : compiler.function.code.length+1 ≤ U32.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_IF)
    (reference : code.step source st data env ctx code.OP_IF before = .ok (.Ok (),out,after)) :
    code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_IF compiler ⦃ result => result.1 = .Ok () ∧ result.2.1 = out ∧
        CompilationBudgetEffect compiler.budget result.2.2.budget
          (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  obtain ⟨bt,remaining,_,read,post⟩ := reader_if_wasm1 p source before after out byte reference
  obtain ⟨signature,selected,_⟩ := wasm1_signature_select compiler.signatures bt
  have conditionLayout : compiler.reachable = true → code.LabelKind.Then = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32]) := by
    intro live _
    obtain ⟨front,_,oldTypes,_⟩ := post.callback_inputs (monomorphic live) (invariant.known live)
      (invariant.live live).2.layout
    refine ⟨front,?_⟩
    have layout := (invariant.live live).2.layout
    simpa [Wasm1.Frames.Form.inputs] using oldTypes ▸ layout
  have callback := compiler_enter_available ops bound available compiler out demand scope
    (Wasm1.Frames.Saved.fresh out .then_ bt).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl)
    .Then (Control.signature bt) signature post.front.1 selected
    (by simp [Wasm1.Frames.Saved.fresh,Control.frame,alloc.vec.Vec.len]) pcRoom conditionLayout
  rw [OpDispatch.dispatch_if]
  exact CoreVisitor.run.available_of_read (code.read_if st data)
    (fun v state bt => (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops).on_if
      v state (Control.signature bt)) compiler bt out
    (fun after => CompilationBudgetEffect compiler.budget after.budget
      (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0)) read callback

end Exec.Code
