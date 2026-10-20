import Exec.Code.Body.Reader.Control.StructuredScopeEntryInstructionPrefix
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackInputs
import Exec.Code.Body.Callbacks.Calls.ScopeCallbackDormantInputs
import Exec.Code.Body.Reader.Common.ReaderReachability

namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve instruction
checks from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_open_instructions_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (held : CompilerInstructionPrefix before)
    (form : Wasm2.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 form.opcode before = .ok (.Ok (),out,after)) :
    CompilerInstructionPrefix after := by
  obtain ⟨bt,ins,outs,remaining,base,callback,_,post⟩ := reader_enter_wasm2 p form initialForm
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨signature,selected,_⟩ := signatures.select post.inputs post.outputs
  obtain ⟨controls,valuesFit,_,_⟩ := post.front initialForm
  have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
    have size := p.size
    have inside := p.inbounds
    change p.start.val < data.val.length at inside
    norm_num [limits.MAX_FUNCTION_BYTES,limits.MAX_MODULE_BYTES] at size ⊢
    omega
  have called : runtime.compiler.control.FunctionCompiler.enter ops before out.core form.kind bt = .ok (.Ok (),after) := by
    rcases initialForm with rfl | rfl | rfl <;> exact callback
  have ifLayout : form.kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]) := by
    intro thenKind live
    have formThen : form = .then_ := by
      rcases initialForm with rfl | rfl | rfl <;> simp_all [Wasm2.Frames.Form.kind]
    have layout := (invariant.live live).2.layout
    obtain ⟨front,_,oldTypes,_,_,_,_,_,_,_,_⟩ := post.callback_inputs initialForm
      (reach.current live) (invariant.known live) layout signatures
    refine ⟨front ++ ins.map Translate.valueType,?_⟩
    simpa only [oldTypes,formThen,Wasm2.Frames.Form.args,List.append_assoc] using layout
  apply structured_scope_entry_open_instructions ops law invariant sourceBound out.core
    (Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout held called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Wasm2.Frames.Form.kind]

end Exec.Code
