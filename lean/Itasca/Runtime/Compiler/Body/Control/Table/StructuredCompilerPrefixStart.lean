import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefix
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixInitial
import Itasca.Runtime.Compiler.Local.Source.SourceStartFrame

/-!
Initial structured prefixes and the compiler function-start callback. The initial prefix certificate is lifted to the actual started compiler state.
-/

/-! ## Structured Prefix Initial -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
theorem StructuredUniversalPrefix.initial {jumpTables : List Aeneas.Std.U32} {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (frame : runtime.compiler.Frame)
    (code : compiler.function.code.val = []) (frames : compiler.frames.val = [frame])
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (localTypes : compilerLocals compiler = locals) (layout : CompilerLayout compiler []) :
    StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals [] (SourceScope.initial returns) [] := by
  refine ⟨localTypes, layout, ?_, ?_⟩
  · intro f member
    simp only [frames, List.mem_singleton] at member
    subst f
    exact ⟨by simp [ForwardSites, noBranches], by simp [noGuard]⟩
  · intro label labels groups plans shape parentShapes
    cases parentShapes
    refine ⟨.root _, ?_⟩
    simpa only [SourceScope.initial, SourceScope.input, List.nil_append, code, List.length_nil] using
      StructuredPrefix.empty emit types functions returns locals (resolvedCode compiler.function.code.val groups)
        [label] [] 0

/-- At function entry there are no completed ELSE arms, including in the
empty saved parent chain. -/
theorem StructuredUniversalElse.initial {jumpTables : List Aeneas.Std.U32} {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype) :
    StructuredUniversalElse (jumpTables := jumpTables) emit compiler types functions returns locals [] (SourceScope.initial returns) := by
  intro label labels groups plans shape parentShapes
  cases parentShapes
  exact .cons _ label (by simp [StructuredElseEvidence, SourceScope.initial]) .nil

end Itasca.Runtime.Compiler

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
theorem StructuredCompilerPrefix.initial {jumpTables : List Aeneas.Std.U32} {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (emit : List valtype → instr → List Bytecode → List valtype → Prop)
    (types functions : List functype) (returns locals : List valtype)
    (frames : ScopeFrameStack locals compiler [] (SourceScope.initial returns))
    (retained : StructuredUniversalPrefix (jumpTables := jumpTables) emit compiler types functions returns locals [] (SourceScope.initial returns) [])
    (arms : StructuredUniversalElse (jumpTables := jumpTables) emit compiler types functions returns locals [] (SourceScope.initial returns))
    (sources : SourceAligned compiler) (codeBudget : SourceCodeBudget compiler 0)
    (controlBudget : SourceControlBudget compiler 0) (cursor : compiler.next_source.val = 0)
    (reachable : compiler.reachable = true) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit compiler compiler types functions returns locals [] (SourceScope.initial returns) [] 0 := by
  refine ⟨.refl _, frames, .root _ rfl, frames.dormant_initial rfl, ScopeConditions.initial, ?_, .live reachable rfl retained, arms, sources, codeBudget, controlBudget, ?_⟩
  · simp [ConcreteStack]
  · omega

end Itasca.Runtime.Compiler

end

/-! ## Structured Compiler Prefix Start -/

section

namespace Itasca.Runtime.Compiler
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
end Itasca.Runtime.Compiler

end
