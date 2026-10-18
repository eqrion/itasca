import Exec.Code.Body.Reader.Common.ReaderPrefixEndDormant
import Exec.Code.Body.Callbacks.Control.CompilerPrefixCloseLoop
import Exec.Code.Body.Callbacks.Control.CompilerPrefixCloseIf
import Exec.Code.Body.Callbacks.Control.CompilerPrefixCloseElse
import Exec.Code.Local.Relations.Control.ControlObservedLayout
namespace Exec.Code
open Aeneas Aeneas.Std Itasca

theorem callback_end_block_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : CompilerPrefix initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .block sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents
      (parent.advance (.BLOCK sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Block := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_block entered stack stable maps frame target sourceType
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])

theorem callback_end_loop_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : CompilerPrefix initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .loop sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents
      (parent.advance (.LOOP sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Loop := by simpa [form, ScopeForm.kind] using shape.kind
  obtain ⟨noFixups, noExit⟩ := shape.loopClean sourceType form
  have unchanged : after.function.code.val = before.function.code.val := by simpa [noFixups, patchCode] using codeEq
  have exit : after.reachable = before.reachable := by simpa [scopeExitLive, frameKind, noExit] using reachable
  exact invariant.close_loop entered stack stable maps frame target sourceType framesEq targetAt unchanged form signature
    exit layout sourceTypes sources consumed (by rw [cursor])

theorem callback_end_if_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : CompilerPrefix initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32)
    (form : current.form = .then_ sourceType condition)
    (signature : BlockSignature types sourceType current.params current.results)
    (sameTypes : current.params = current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType current.source [])) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, guard, framesEq, shape, targetAt, guardEq, guardCode, live, codeEq⟩ :=
    invariant.end_guarded ops law sourceType condition form entered state kind bt coordinate sourceBound accepted
  exact invariant.close_if entered stack stable maps frame target sourceType guard condition core.num.U32.MAX
    framesEq guardEq guardCode targetAt codeEq form signature sameTypes live layout sourceTypes sources consumed (by rw [cursor])

theorem callback_end_else_prefix {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : CompilerPrefix initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (form : current.form = .else_ sourceType condition yes yesExit noEntry yesNormal)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    CompilerPrefix initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType yes current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Else := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_else entered stack stable maps frame target sourceType condition noEntry yes yesExit yesNormal
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])
end Exec.Code
