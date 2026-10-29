import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedFold
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointIndirectCall
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointNumeric
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointOrdinary
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointControl
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointRoot
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointExtra
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedStateful
import Itasca.Runtime.Compiler.Body.Reader.Simd.IndexedTableCompilerSimd
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Body.Relations.Executable.ExecutableEmission
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchTableIndexed
import Itasca.Runtime.Compiler.Body.Control.Table.IndexedTablePointTypedSelect
import Itasca.Runtime.Compiler.Local.Relations.Syntax.BulkAndSaturatingEncoding
import Itasca.Runtime.Compiler.Local.Lowering.Integer.NumericEncoding
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignEmissions
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceCursor
import Itasca.Runtime.Compiler.Local.Relations.Operations.DeadCode
import Itasca.Runtime.Compiler.Body.Reader.Replay.ProfileAgreement
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownNumericStack
import Itasca.Runtime.Compiler.Body.Reader.Scalar.SignExtension
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Scalar.NumericEmissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.IntegerFacts
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Emissions
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Empty
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralSources
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Lowering.Integer.LoweringArithmetic
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal
import Itasca.Runtime.Compiler.Local.Lowering.Literal.LiteralCursor
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerLiteralMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerMetadataTactic
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEmissions
import Itasca.Runtime.Compiler.Body.Reader.Local.LocalEffects
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallLowering
import Itasca.Support.EnvTranslation
import Itasca.Runtime.Compiler.Body.Reader.Calls.CallEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerOrdinaryResults
import Itasca.Runtime.Compiler.Local.Capacity.EmissionGrowth
import Itasca.Runtime.Compiler.Body.Reader.Scalar.Unreachable
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Lowering.Control.LoweringReturn
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReturnStack
import Itasca.Runtime.Compiler.Body.Reader.Control.RootFrame
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FramePlanPop
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseFrames
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackEnter
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlEntrySuccess
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerEnterMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlCursor
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlSources
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Callbacks.Calls.ScopeCallbackInputs
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.CompilerBounds

/-!
Actual accepted complete-profile body execution produces indexed code evidence against all four final function-local tables.

Main declarations: `TypedRunWasm2.compile_executable`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca
/-- Actual accepted complete-profile body execution produces indexed code
evidence against all four final function-local tables. -/
theorem TypedRunWasm2.compile_executable {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before final : runtime.compiler.FunctionCompiler A}
    {locals data env ctx index ft st source}
    (C : context)
    (run : TypedRunWasm2 (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) data env ctx index st before final)
    (point : IndexedTableReaderCompilerPointWasm2 (fun tables => ExecutableEmission tables C) initial before (env.types.val.map EnvTranslation.funcType)
      (env.func_types.val.map EnvTranslation.funcType) (ft.results.val.map Translate.valueType) locals data env ctx.locals index ft st)
    (encoded : Wasm2.BodyEncoding data source)
    (initialLocals : LocalLayout initial) (localsMatch : initial.function.locals = ctx.locals)
    (metadata : FunctionParameterSlots initial env)
    (matched : EnvTranslation.Matches env ⟨ctx.locals,ft.results⟩ C)
    (contextLocals : C.LOCALS = locals)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (bodyBound : initial.function.body_start.val + data.length ≤ Usize.max) :
    StructuredCompiledBody final.function.jump_tables.val ((fun tables => ExecutableEmission tables C) (CompilerTables.ofFunction final.function)) initial final
      (env.types.val.map EnvTranslation.funcType) (env.func_types.val.map EnvTranslation.funcType)
      (ft.results.val.map Translate.valueType) locals source := by
  apply TypedRunWasm2.fold_indexed_tables ops (fun tables => ExecutableEmission tables C) initial _ _ _ _ data env ctx index ft source ?_ run point
  intro st before middle final next out point advance inbounds accepted rest
  obtain ⟨parents,current,savedParents,savedCurrent,state⟩ := point.future CompilerTables.empty
  have sourceBound := state.boundary.source_bound
  have bodyBound := state.compiled.metadata.body_bound bodyBound
  have allowed := encoded.next_reader_opcode state.boundary.consumed inbounds
  rcases allowed with ordinary | scope | isElse | isEnd | extra | floatBase | memoryOp | indirect | table | statefulOp | prefixed | simd | typedSelect
  · exact .inr (point.ordinary ops law contextLocals (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) metadata localsMatch next advance inbounds out sourceBound bodyBound
      _ ordinary rfl accepted)
  · exact .inr (point.scope_step ops law next advance inbounds out sourceBound signatures _ scope rfl accepted)
  · rw [isElse] at accepted
    exact .inr (point.else_ ops law next advance inbounds out initialLocals
      (by simpa only [global_simps] using isElse) (by simpa only [global_simps] using accepted))
  · rw [isEnd] at accepted
    by_cases root : st.blocks.val.length = 1
    · exact .inl (point.finish_root ops law root next advance inbounds out sourceBound bodyBound encoded isEnd accepted rest)
    · exact .inr (point.end_nested ops law next advance inbounds out initialLocals rfl root bodyBound
        (by simpa only [global_simps] using isEnd) (by simpa only [global_simps] using accepted))
  · exact .inr (point.core_extra ops law C (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals matched.globals matched.mems
      next advance inbounds out sourceBound bodyBound _ extra rfl accepted)
  · obtain ⟨op,baseOpcode,equal⟩ := float_base_opcode_of_mem floatBase
    rw [← equal] at accepted
    exact .inr (point.float_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op baseOpcode sourceBound bodyBound equal.symm accepted)
  · have stateful := stateful_opcode_values (.inl memoryOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · rw [indirect] at accepted
    exact .inr (point.indirect_call ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C)))
      matched contextLocals signatures next advance inbounds out sourceBound bodyBound indirect accepted)
  · rw [table] at accepted
    exact .inr (point.br_table ops law next advance inbounds out
      (by intro tables depths fallback stack selector start len; exact .branchTable _ _ _ _ _ _) table accepted)
  · have stateful := stateful_opcode_values (.inr statefulOp)
    exact .inr (point.stateful_base ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out _ stateful
      sourceBound bodyBound rfl accepted)
  · obtain ⟨subopcode,endPosition,decoded,choice⟩ :=
      encoded.next_misc state.boundary.consumed inbounds next advance prefixed
    rw [prefixed] at accepted
    rcases choice with ⟨op,extension,subopcodeEq⟩ | bulk
    · exact .inr (point.float_saturating ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) contextLocals next advance inbounds out op extension
        subopcode endPosition subopcodeEq decoded sourceBound bodyBound prefixed accepted)
    · exact .inr (point.stateful_bulk ops law (fun tables => (inferInstance : OrdinaryEmbedding tables.indirect C (ExecutableEmission tables C))) matched contextLocals next advance inbounds out subopcode endPosition bulk
        sourceBound bodyBound prefixed decoded accepted)
  · rw [simd] at accepted
    exact .inr (point.simd ops law C contextLocals matched.mems (fun tables => (inferInstance : SimdEmbedding tables.simd tables.constants C (ExecutableEmission tables C))) next advance inbounds out sourceBound bodyBound simd accepted)
  · rw [typedSelect] at accepted
    exact .inr (point.typed_select ops law C (by intro tables input instruction code output h; exact .typedSelect h) contextLocals next advance inbounds out sourceBound bodyBound typedSelect accepted)
end Itasca.Runtime.Code
