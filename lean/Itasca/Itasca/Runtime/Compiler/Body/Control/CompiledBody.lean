import Itasca.Runtime.Compiler.Body.Reader.Stateful.ExtendedCapacity
import Itasca.Runtime.Compiler.Body.Reader.Calls.Acceptance
import Itasca.Runtime.Compiler.Body.Reader.Replay.ReaderCompilerState
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Body.Control.BranchesAndDormantEntry
import Itasca.Runtime.Compiler.Body.Control.StructuredPrefixes
import Itasca.Runtime.Compiler.Local.Control.Structured.Prefixes
import Itasca.Runtime.Compiler.Local.Control.Structured.NestedScopes
import Itasca.Runtime.Compiler.Body.Callbacks.CompilerPrefixStart
import Itasca.Runtime.Compiler.Local.Control.CodeSegmentsAndPositions
import Itasca.Runtime.Compiler.Local.Relations.Prefix.SuspendedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.PrefixZipper
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.MetadataPreservation
import Itasca.Runtime.Compiler.Local.Relations.Stateful.StatefulLowered
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Replay.MetadataTypes
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CallbackRetention
import Itasca.Runtime.Compiler.Body.Reader.Control.EndCompilation
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EntryAndElseFrames
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCoordinates
import Itasca.Runtime.Compiler.Body.Callbacks.ScopeInputs
import Itasca.Runtime.Compiler.Local.Relations.Stacks.ConcretePops
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalRoot
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchAndCallMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.TypedRunClosed
import Itasca.Runtime.Compiler.Body.Relations.Control.ReachedControlSafety
import Itasca.Runtime.Compiler.Local.Control.StructuredElseResolvedAppend
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ResolvedGuards
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.RootLabel
import Itasca.Runtime.Compiler.Body.Reader.StackValues

open WebAssembly

/-!
Proofs for Runtime / Compiler / Body / Control.

This module collects CompiledBody, OpenPrefixes, RootBoundary.
Each section documents its contracts and consumers.
-/

/-! ## CompiledBody -/

section

open Itasca.Representation

/-!
# Compiled Body

Indexed instruction points assemble a compiled body. Indirect-call cases and the final structured-body construction share the same retained compiler invariant.
-/

/-! ## IndexedTablePointIndirectCall -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem IndexedTableReaderCompilerPoint.indirect_call {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {C types functions returns locals data env ctx index ft st}
    {emit : CompilerTables → List valtype → instr → List Bytecode → List valtype → Prop}
    (point : IndexedTableReaderCompilerPoint emit initial before types functions returns locals data env ctx.locals index ft st)
    (embedding : ∀ tables, OrdinaryEmbedding tables.indirect C (emit tables))
    (matched : Translation.Environment.Matches env ⟨ctx.locals,ft.results⟩ C) (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = 17#u8)
    (accepted : code.step_body (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index 17#u8 before = .ok (.Ok (),out,after)) :
    IndexedTableReaderCompilerPoint emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  obtain ⟨extra,pairs⟩ := reader_indirect_call_pair_prefix p ops law initial before after out ctx C
    state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  obtain ⟨idx,tab,_,callback,_,_⟩ := reader_indirect_call p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  change runtime.compiler.lower.FunctionCompiler.op ops before out.core 17#u16 idx tab 0#u128 = _ at callback
  have auxiliary := compiler_indirect_call_auxiliary_tables ops law before after out.core idx tab (.Ok ()) callback
  have tables := compiler_tables_pair_append before.function after.function extra pairs auxiliary
  have depths := reader_indirect_call_depths p ops law before after out ctx byte accepted
  have growth := reader_indirect_call_code_mono p ops law before after out ctx byte accepted
  have jumps : after.function.jump_tables.val = before.function.jump_tables.val := by
    have h := congrArg CompilerTables.jumpTables tables
    simpa only [CompilerTables.ofFunction,CompilerTables.append,List.append_nil] using h
  have boundary : CompilerTableBoundary after :=
    ⟨by simpa only [depths] using point.tables.depths,
      by simpa only [jumps] using point.tables.targets.trans growth⟩
  apply point.append_step ⟨extra,[],[],[]⟩ tables boundary
  intro future old
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := old
  let p := state.boundary.pending next advance inbounds
  obtain ⟨typeIndex,table,values,extra,pairs,reader,compiled,reachable⟩ :=
    structured_reader_prefix_indirect_call p ops law initial before after out ctx C future.indirect
      (fun _ _ _ _ head => (embedding ((CompilerTables.ofFunction after.function).append future)).indirect (head)) state.compiled state.reach.current matched contextLocals signaturesBefore sourceBound bodyBound byte accepted
  exact (state.advance next advance inbounds reader (by simp [Spec.DeclaredReferences.Instruction,Spec.DeclaredReferences.instructionIndices]) compiled
    (fun live => state.reach.current (reachable ▸ live))).point
end Itasca.Compiler

end

/-! ## StructuredLinearEmbedding -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredCompilerPrefix.ordinary_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction emitted output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLowered before after nextRaw emitted output)
    (emission : LinearEmission locals (Body.Stack.stackTypes raw) instruction [emitted] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branch_table

theorem StructuredCompilerPrefix.ordinary_empty_linear {jumpTables : List U32} {A : Type}
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition instruction output}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (embedding : LinearEmbedding locals emit)
    (reachable : before.reachable = true) (ordinary : CompilerOrdinaryStable before after)
    (lowered : TypedLoweredEmpty before after nextRaw output)
    (emission : LinearEmission locals (Body.Stack.stackTypes raw) instruction [] output)
    (sources : SourceProgress before after) (consumed : position < nextPosition)
    (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents (current.advance instruction) nextRaw nextPosition :=
  invariant.ordinary_empty reachable ordinary lowered (embedding emission) sources consumed cursor emission.not_branch_table
end Itasca.Compiler

end

/-! ## StructuredCompiledBody -/

section

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca
/-- Completed source-to-bytecode evidence, before the compiler's final
well-formedness check packages the executable function. -/
def StructuredCompiledBody (jumpTables : List U32) (emit : List valtype → instr → List Bytecode → List valtype → Prop) {A : Type} (initial final : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype) (source : List instr) : Prop :=
  ∃ target : U32, CompilerStable initial final ∧ final.frames.val = [] ∧
    StructuredCode emit types functions returns locals final.function.code.val jumpTables
      [functionRootLabel returns final.function target] [] source 0 target.val returns ∧
    (∃ src count, src.val = slots locals ∧ final.function.code.val[target.val]? = some (.Return src count)) ∧
    final.function.code.val.length = target.val + 1 ∧ final.function.code.val.length ≤ U32.max

end Itasca.Compiler

end

end

/-! ## OpenPrefixes -/

section

/-!
# Opening structured compiler prefixes

Exact control-entry effects preserve the retained compiler invariant. Future exit coordinates remain quantified until the matching END or ELSE establishes their values.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

/-- Exact entry effects preserve the whole retained invariant. The future
exit coordinates stay quantified until the corresponding END or ELSE. -/
theorem StructuredCompilerPrefix.open_plain {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (child : SourceScope) (frame : runtime.compiler.Frame) (emitted : List Bytecode)
    (ordinary : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code.val = before.function.code.val ++ emitted)
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (noGuard : frame.if_pc = none) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (childCondition : ScopeCondition locals child)
    (layout : CompilerLayout after (Body.Stack.stackTypes raw))
    (sourceTypes : SourceStack nextRaw (Body.Stack.stackTypes raw))
    (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = Body.Stack.stackTypes raw) (arguments : child.arguments = Body.Stack.stackTypes raw)
    (sources : SourceProgress before after) (growth : emitted.length ≤ 3)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.fields.2.2.2.2.1]; exact retained.localsEq
  have next := retained.open_plain child frame emitted codeEq framesEq noGuard noBranches localsEq layout
    entered childEntered entry body source input arguments
  have growthEq : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append]; omega
  refine ⟨invariant.metadata.trans ordinary, aligned,
    invariant.entryChain.push child (fun _ => entered),
    (by rw [framesEq]; exact invariant.dormant.push frame clean), invariant.conditions.push child childCondition, (fun _ => sourceTypes.concrete),
    .live live childEntered ?_,
    invariant.arms.open_plain retained.sites child frame emitted fresh codeEq framesEq noGuard noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growthEq consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  simpa only [sourceTypes.decoded] using next

theorem StructuredCompilerPrefix.open_if {jumpTables : List Aeneas.Std.U32} {A : Type} {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals parents current raw position nextRaw nextPosition stack}
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals parents current raw position)
    (reachable : before.reachable = true) (live : after.reachable = true)
    (child : SourceScope) (frame : runtime.compiler.Frame) (condition : U32) (site : Usize)
    (sitePosition : site.val = before.function.code.val.length)
    (inputStack : Body.Stack.stackTypes raw = stack ++ [.I32])
    (ordinary : CompilerStable before after)
    (aligned : ScopeFrameStack locals after (parents ++ [current]) child)
    (codeEq : after.function.code.val = before.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX])
    (framesEq : after.frames.val = before.frames.val ++ [frame])
    (maps : after.function.controls.val.length = before.function.controls.val.length + 1)
    (guardEq : frame.if_pc = some site) (noBranches : frame.fixups.val = [])
    (clean : DormantFrame frame) (fresh : child.form.isElse = false)
    (childCondition : ScopeCondition locals child)
    (layout : CompilerLayout after stack)
    (sourceTypes : SourceStack nextRaw stack)
    (childEntered : child.entered = true)
    (entry : child.entry = before.function.code.val.length)
    (body : child.bodyPc = after.function.code.val.length) (source : child.source = [])
    (input : child.input = stack) (arguments : child.arguments = stack ++ [.I32])
    (sources : SourceProgress before after)
    (consumed : position < nextPosition) (cursor : after.next_source.val ≤ nextPosition) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals (parents ++ [current]) child nextRaw nextPosition := by
  obtain ⟨entered, retained⟩ := invariant.live reachable
  have localsEq : compilerLocals after = locals := by
    rw [compilerLocals, ordinary.fields.2.2.2.2.1]; exact retained.localsEq
  have next := (inputStack ▸ retained).open_if child frame condition site sitePosition codeEq framesEq guardEq noBranches localsEq layout
    entered childEntered entry body source input arguments
  have growthEq : after.function.code.val.length ≤ before.function.code.val.length + 3 := by
    rw [codeEq, List.length_append, List.length_singleton]; omega
  refine ⟨invariant.metadata.trans ordinary, aligned,
    invariant.entryChain.push child (fun _ => entered),
    (by rw [framesEq]; exact invariant.dormant.push frame clean), invariant.conditions.push child childCondition, (fun _ => sourceTypes.concrete),
    .live live childEntered ?_,
    invariant.arms.open_if retained.sites child frame condition site fresh sitePosition codeEq framesEq guardEq noBranches,
    sources.aligned invariant.sources, invariant.codeBudget.advance growthEq consumed,
    invariant.controlBudget.enter maps (by simp [framesEq]) consumed, cursor⟩
  simpa only [sourceTypes.decoded] using next

end Itasca.Compiler

end

/-! ## RootBoundary -/

section

/-!
# Root control-boundary correspondence

The reader boundary is a root precisely when its retained control state has the root shape. Structured compiler points use this correspondence when closing complete bodies.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca

theorem ReaderBoundary.root_iff {data env locals index ft st parents current}
    (boundary : ReaderBoundary data env locals index ft st parents current) :
    current.form = .body ↔ st.blocks.val.length = 1 := by
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := boundary.opened
  constructor
  · intro form
    have empty := (form ▸ spine).body.1
    simp [blocks,empty]
  · intro count
    have empty : parents = [] := by simpa [blocks] using count
    generalize formEq : current.form = form at spine ⊢
    cases spine with
    | root => rfl
    | push => simp at empty

end Itasca.Compiler

end
