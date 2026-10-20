import Exec.Code.Body.Reader.Control.StructuredScopeEntryExitSlots
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackDormantInputs
import Exec.Code.Body.Reader.Common.ReaderReachability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- The canonical Wasm 1 entry postcondition supplies signature and physical
control geometry in both live and dormant source code. -/
theorem ReaderEnterPostWasm1.exit_slots {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env ctx bodyBt st out form bt remaining token} {p : Wasm1.Pending data env ctx bodyBt st}
    (post : ReaderEnterPostWasm1 p out form bt remaining token) (initialForm : form.Initial)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current}
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (held : FrameExitSlotBounds before)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before out form.kind (Control.signature bt) = .ok (.Ok (),after)) :
    FrameExitSlotBounds after := by
  obtain ⟨signature,selected,_⟩ := wasm1_signature_select before.signatures bt
  obtain ⟨controls,base,_⟩ := post.front
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have ifLayout : form.kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]) := by
    intro thenKind live
    have formThen : form = .then_ := by
      rcases initialForm with rfl | rfl | rfl <;> simp_all [Wasm1.Frames.Form.kind]
    have layout := (invariant.live live).2.layout
    obtain ⟨front,_,oldTypes,_,_,_,_,_,_,_,_⟩ := post.callback_inputs
      (reach.current live) (invariant.known live) layout
    refine ⟨front,?_⟩
    simpa only [oldTypes,formThen,Wasm1.Frames.Form.inputs] using layout
  apply structured_scope_entry_exit_slots ops law invariant sourceBound out
    (Wasm1.Frames.Saved.fresh out form bt).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm1.Frames.Saved.ctrl)
    form.kind (Control.signature bt) signature _ controls selected (by rw [base]) ifLayout held called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Wasm1.Frames.Form.kind]

/-- All three Wasm 1 scope-opening readers preserve recorded exit-slot bounds. -/
theorem reader_enter_exit_slots_wasm1 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env ctx bodyBt st} (p : Wasm1.Pending data env ctx bodyBt st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.vals.val p.start.val)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (held : FrameExitSlotBounds before)
    (opcode : U8) (allowed : opcode = code.OP_BLOCK ∨ opcode = code.OP_LOOP ∨ opcode = code.OP_IF)
    (byte : data.val[p.start.val]'p.inbounds = opcode)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx opcode before = .ok (.Ok (),out,after)) :
    FrameExitSlotBounds after := by
  rcases allowed with rfl | rfl | rfl
  · obtain ⟨bt,callback,_,post⟩ := reader_block_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact post.exit_slots (.inl rfl) ops law invariant reach held callback
  · obtain ⟨bt,callback,_,post⟩ := reader_loop_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact post.exit_slots (.inr (.inl rfl)) ops law invariant reach held callback
  · obtain ⟨bt,remaining,callback,_,post⟩ := reader_if_wasm1 p
      (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
    exact post.exit_slots (.inr (.inr rfl)) ops law invariant reach held callback

end Exec.Code
