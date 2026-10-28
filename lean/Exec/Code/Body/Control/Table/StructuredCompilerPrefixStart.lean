import Exec.Code.Body.Control.Table.StructuredPrefixInitial
import Exec.Code.Local.Source.SourceStartFrame
namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std

/-- Actual construction and successful function-start establish every component
of the compiler prefix invariant, before the first source opcode is read. -/
theorem structured_compiler_function_start_prefix {jumpTables : List Aeneas.Std.U32} (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (ops : runtime.platform.Alloc A)
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
    StructuredCompilerPrefix (jumpTables := jumpTables) emit started started types functions returns (ctx.locals.val.map Itasca.Translate.valueType)
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
  have codeEmpty : started.function.code.val = [] := by
    have length : started.function.code.val.length = 0 := by
      have bound := codeBudget
      change started.function.code.val.length ≤ 3 * 0 at bound
      omega
    simpa only [List.length_eq_zero_iff] using length
  have sites := retained.sites frame (by simp [frames])
  have noGuard : frame.if_pc = none := by
    cases guard : frame.if_pc with
    | none => rfl
    | some site =>
      obtain ⟨condition, target, found⟩ := sites.guard site guard
      simp [codeEmpty] at found
  have noBranches : frame.fixups.val = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro site member
    have bound := sites.branches.inside site member
    simp [codeEmpty] at bound
  have next := StructuredUniversalPrefix.initial (jumpTables := jumpTables) started emit types functions returns _ frame
    codeEmpty frames noGuard noBranches retained.localsEq retained.layout
  exact StructuredCompilerPrefix.initial started emit types functions returns _ stack next
    (StructuredUniversalElse.initial started emit types functions returns _)
    (sourceFrame.sources.aligned initialSources) codeBudget controlBudget
    (by rw [sourceFrame.cursor, newCursor]; rfl) live
end Itasca.Runtime.Code
