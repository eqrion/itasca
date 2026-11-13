import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefixStart
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Calls.IndirectCallMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Body.Control.Control.CumulativePointControl
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredScopes
import Itasca.Runtime.Compiler.Body.Reader.Control.ElseCompilation
import Itasca.Runtime.Compiler.Body.Reader.Control.EndWasm2Compilation
import Itasca.Runtime.Compiler.Body.Reader.Control.RootCompilation
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Source.SourceEntry

/-!
Sections, each formerly its own module: IndexedTablePointControl, StructuredCompilerPrefixStart.
-/

/-! ## IndexedTablePointControl -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPointWasm2.scope_step {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index opcode before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_control_effects_wasm2 ops law before after _ out data env ctx _ opcode (.inl supported) accepted
  have pairs := effects.tables
  have depths := effects.depths
  have growth := effects.code_mono
  apply point.preserved_step pairs depths growth
  intro future old
  exact old.scope_step ops law next advance inbounds out sourceBound signatures opcode supported byte accepted

theorem IndexedTableReaderCompilerPointWasm2.else_ {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (initialLocals : LocalLayout initial)
    (byte : data.val[st.core.pos.val]'inbounds = 5#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 5#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_else_effects_wasm2 ops law before after _ out data env ctx _ (by simpa only [global_simps] using accepted)
  have pairs := effects.tables
  have depths := effects.depths
  have growth := effects.code_mono
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  exact state.else_ ops law initialLocals next advance inbounds out (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)

theorem IndexedTableReaderCompilerPointWasm2.end_nested {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPointWasm2 emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (initialLocals : LocalLayout initial)
    (typesEq : types = env.types.val.map EnvTranslation.funcType)
    (nonRoot : st.blocks.val.length ≠ 1)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 11#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 11#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPointWasm2 emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have effects := reader_end_effects_wasm2 ops law before after _ out data env ctx _ (by simpa only [global_simps] using accepted)
  have pairs := effects.tables
  have depths := effects.depths
  have growth := effects.code_mono
  apply point.preserved_step pairs depths growth
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  have form : savedCurrent.form ≠ .body := fun h => nonRoot (state.boundary.root_iff.mp h)
  exact state.end_nested ops law initialLocals typesEq next advance inbounds out form bodyBound
    (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
end Itasca.Runtime.Compiler

end

/-! ## StructuredCompilerPrefixStart -/

section

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

end
