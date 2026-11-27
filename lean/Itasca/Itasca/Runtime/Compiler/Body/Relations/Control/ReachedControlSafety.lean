import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Bounds
import Itasca.Runtime.Compiler.Local.Relations.Operations.TerminalAndPairSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeEffects
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSkipSafety
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Relations / Control.

This module collects BranchIfLayout, ReachedControlSafety.
Each section documents its contracts and consumers.
-/

/-! ## BranchIfLayout -/

section

open Itasca.Representation

/-!
# Conditional branch layout

Condition slots and resumed source-code budgets relate BR_IF lowering to the retained compiler layout. Branch acceptance and compilation compose these facts.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem CompilerLayout.condition {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {stack : List valtype} (layout : CompilerLayout compiler (stack ++ [.I32])) :
    ∃ condition : U32,
      compiler.before.val[compiler.before.val.length - 1]? = some condition ∧
      condition.val = slots (compilerLocals compiler) + slots stack := by
  have length := layout.operands_length
  simp only [List.length_append, List.length_singleton] at length
  have bound : stack.length < compiler.before.val.length := by omega
  let condition := compiler.before.val[stack.length]'bound
  have atIndex : compiler.before.val[stack.length]? = some condition := List.getElem?_eq_getElem bound
  refine ⟨condition, ?_, ?_⟩
  · have index : compiler.before.val.length - 1 = stack.length := by omega
    simpa only [index] using atIndex
  · have mapped := congrArg (fun list => list[stack.length]?) layout.operandOffsets
    simpa [stackOffsets, List.getElem?_map, atIndex, offset] using mapped

theorem SourceCodeBudget.branch_resume {A : Type} {compiler : runtime.compiler.FunctionCompiler A}
    {position : Nat} (budget : SourceCodeBudget compiler position)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (count source destination : U32) :
    ∃ resume : U32, resume.val = compiler.function.code.val.length +
      (if count = 0#u32 ∨ source = destination then 1 else 3) := by
  have fits : compiler.function.code.val.length + 3 < 2^32 := by
    unfold SourceCodeBudget at budget
    norm_num [limits.MAX_MODULE_BYTES] at sourceBound
    omega
  let pc := compiler.function.code.val.length + (if count = 0#u32 ∨ source = destination then 1 else 3)
  have bound : pc < 2^32 := by dsimp [pc]; split <;> omega
  exact ⟨UScalar.ofNatCore pc bound, rfl⟩
end Itasca.Compiler

end

/-! ## ReachedControlSafety -/

section

/-!
# Reached END and ELSE safety

Reached control callbacks use retained physical frame, map and fixup sites to return normally. The validator may already have closed its own frame before the callback runs.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

 theorem ScopeFrameShape.body_guard {locals scope frame}
    (shape : ScopeFrameShape locals scope frame) (body : frame.kind = .Body) : frame.if_pc = none := by
  have kind := shape.kind.symm.trans body
  have guard := shape.guard
  cases form : scope.form <;> simp [form,ScopeForm.kind] at kind
  simp [SourceScope.guardPosition,form] at guard
  exact guard

/-- Every reached END uses the retained physical frame, map and fixup sites.
The validator may already have closed its own frame before invoking the hook. -/
theorem StructuredCompilerPrefix.end_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (coordinate : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (emitCoordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  let rest := alloc.vec.Vec.from prior (by have := compiler.frames.property; simp only [frames,List.length_append,List.length_singleton] at this; omega)
  have room := invariant.codeBudget.callback_headroom bounded invariant.sources
  exact compiler_end_total ops law compiler state frame rest kind bt (by simpa [rest] using frames)
    (invariant.mode.sites frame (by simp [frames])) shape.toScopeFrameShape.body_guard shape.mapBound
    (by omega) coordinate (by omega) (by omega) emitCoordinate

 theorem StructuredCompilerPrefix.else_total {jumpTables : List U32} {A}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial compiler : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial compiler types functions returns locals parents current raw position)
    (bounded : position ≤ Itasca.limits.MAX_MODULE_BYTES.val)
    (fixups : FixupBudget compiler.frames.val compiler.function.code.val.length)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (coordinate : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have member : frame ∈ compiler.frames.val := by simp [frames]
  have room := invariant.codeBudget.callback_headroom bounded invariant.sources
  exact compiler_else_total ops law compiler state bt frame prior frames (invariant.mode.sites frame member)
    ((fixups frame member).trans_lt (by omega)) (by omega) (by omega) (by omega) coordinate
end Itasca.Compiler

end
