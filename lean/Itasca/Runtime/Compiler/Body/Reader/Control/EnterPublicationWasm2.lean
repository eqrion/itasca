import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Publication.ScopeEntryPublication
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability

/-!
Structured compiler scope-entry source map publication and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Scope Entry Publication -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca

/-- A reached structured prefix supplies entry PC and reserve bounds. Actual
checked entry supplies arithmetic bounds, including dormant stack heights.
The reader contributes only its selected control/signature and live IF stack. -/
theorem structured_scope_entry_publication {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals parents current raw position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (ctrl : code.Ctrl) (prior : List code.Ctrl)
    (kind : code.LabelKind) (bt : signature.BlockType) (signature : runtime.compiler.Signature)
    (allowed : kind = .Block ∨ kind = .Loop ∨ kind = .Then)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt before.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (ifLayout : kind = .Then → before.reachable = true → ∃ stack, CompilerLayout before (stack ++ [.I32]))
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val)
    (forward : before.next_source.val ≤ state.pos.val)
    (called : runtime.compiler.control.FunctionCompiler.enter ops before state kind bt = .ok (.Ok (),after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
  obtain ⟨heightFits,sourceFits⟩ := control_entry_coordinates ops before after state ctrl prior kind bt controls valuesFit called
  obtain ⟨codeFits,offsetsFit,mapsFit,framesFit⟩ := invariant.capacities sourceBound
  have codeBound := invariant.codeBudget.fetch_bound sourceBound
  let makeGeometry (pc : U32) : ScopeEntryGeometry before state bt :=
    ⟨ctrl,prior,signature,pc,controls,selected,valuesFit,heightFits,sourceFits,mapsFit,framesFit⟩
  let pc : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  by_cases live : before.reachable = true
  · rcases allowed with rfl | rfl | rfl
    · exact compiler_scope_entry_publication ops law before after state .Block bt (makeGeometry pc)
        (.block live rfl) coordinates maps inside forward called
    · exact compiler_scope_entry_publication ops law before after state .Loop bt (makeGeometry pc)
        (.loop live rfl codeFits offsetsFit) coordinates maps inside forward called
    · obtain ⟨stack,layout⟩ := ifLayout rfl live
      let guardedPc : U32 := UScalar.ofNatCore (before.function.code.val.length+1) (by scalar_tac)
      exact compiler_scope_entry_publication ops law before after state .Then bt (makeGeometry guardedPc)
        (.if_ stack layout live rfl codeFits offsetsFit) coordinates maps inside forward called
  · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
    exact compiler_scope_entry_publication ops law before after state kind bt (makeGeometry pc)
      (.dead kind dead rfl) coordinates maps inside forward called

end Itasca.Runtime.Code

end

/-! ## Reader Enter Publication Wasm2 -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Actual Wasm 2 BLOCK, LOOP and IF readers preserve both publication
invariants from a reached source prefix, in live and unreachable code. -/
theorem reader_enter_publication_wasm2 {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop}
    {data env localTypes index st} (p : Wasm2.Pending data env .Wasm2 localTypes index st)
    {A : Type} (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals
      parents current st.core.vals.val p.start.val)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (signatures : SignatureSequence before.signatures.val env.types.val)
    (coordinates : SourceCoordinates before) (maps : ControlMapPublication before)
    (extent : before.function.body_end.val = before.function.body_start.val+data.length)
    (form : Wasm2.Frames.Form) (initialForm : form.Initial)
    (byte : data.val[p.start.val]'p.inbounds = form.opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index .Wasm2 form.opcode before = .ok (.Ok (),out,after)) :
    SourceCoordinates after ∧ ControlMapPublication after := by
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
  have consumed : p.start.val < out.core.pos.val := by
    have position := p.pos
    have advanced := post.after.2.1
    omega
  have inside : before.function.body_start.val+before.next_source.val < before.function.body_end.val := by
    have cursor := invariant.cursor
    have bounded := p.inbounds
    change p.start.val < data.length at bounded
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
  apply structured_scope_entry_publication ops law invariant sourceBound out.core
    (Wasm2.Frames.Saved.fresh base form bt ins outs).ctrl
    ((p.parents ++ [{p.current with vals := remaining}]).map Wasm2.Frames.Saved.ctrl)
    form.kind bt signature _ controls selected valuesFit ifLayout coordinates maps inside _ called
  · rcases initialForm with rfl | rfl | rfl <;> simp [Wasm2.Frames.Form.kind]
  · exact le_trans invariant.cursor (Nat.le_of_lt consumed)

end Itasca.Runtime.Code

end
