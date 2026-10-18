import Exec.Code.Body.Callbacks.Common.CompilerPrefixInitial
import Exec.Code.Local.Source.SourceStartFrame
namespace Exec.Code
open Aeneas Aeneas.Std

/-- Actual construction and successful function-start establish every component
of the compiler prefix invariant, before the first source opcode is read. -/
theorem compiler_function_start_prefix {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (signatures : Slice runtime.compiler.Signature)
    (functionSlots : Slice U32) (budget : runtime.compiler.Budget A) (batchStart : Usize)
    (initial started : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize) (types functions : List functype) (returns : List valtype)
    (lookup : signatures.val[typeIndex.val]? = some signature)
    (resultWidth : signature.result_slots.val = slots returns)
    (beginFits : batchStart.val + bodyBegin.val ≤ Usize.max)
    (endFits : batchStart.val + bodyEnd.val ≤ Usize.max)
    (created : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart = .ok initial)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops initial ctx typeIndex bodyBegin bodyEnd = .ok (.Ok (), started)) :
    CompilerPrefix started started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
      [] (SourceScope.initial returns) [] 0 := by
  obtain ⟨frame, frames, shape, retained, arms, codeBudget, controlBudget, stack, live⟩ :=
    compiler_function_start_scope ops law signatures functionSlots budget batchStart initial started ctx
      typeIndex signature bodyBegin bodyEnd types functions returns lookup resultWidth beginFits endFits created accepted
  have sourceFrame := compiler_function_start_source_frame ops law initial started ctx typeIndex bodyBegin bodyEnd
    (.Ok ()) accepted
  have initialSources := compiler_new_sources ops signatures functionSlots budget batchStart
  rw [created, WP.spec_ok] at initialSources
  have newCursor : runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart
      ⦃ out => out.next_source = 0#usize ⦄ := by
    simp [runtime.compiler.FunctionCompiler.new, WP.spec_ok]
  rw [created, WP.spec_ok] at newCursor
  exact CompilerPrefix.initial started types functions returns _ stack retained arms
    (sourceFrame.sources.aligned initialSources) codeBudget controlBudget
    (by rw [sourceFrame.cursor, newCursor]; rfl) live
end Exec.Code
