import Itasca.Runtime.Compiler.Body.Reader.Control.ControlEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Control.CloseWasm2
import Itasca.Runtime.Compiler.Local.Relations.Syntax.ReaderOpcode
import Itasca.Runtime.Compiler.Body.Callbacks.Prefix.CompilerPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.Boundary
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalPrefix
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
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerDeadMetadata
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalDormant
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackDead
import Itasca.Runtime.Compiler.Local.Relations.Stacks.KnownPopStack
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.ScopeCallbackIf
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchLayout
import Itasca.Runtime.Compiler.Local.Control.Prefix.UniversalConditional
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseEvidence
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessCallbacks
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessControls
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCallbackMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackSources
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackCursor
import Itasca.Runtime.Compiler.Body.Reader.Replay.Post
import Itasca.Runtime.Compiler.Local.Source.SourceStacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Control.Control.CumulativePointControl
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved
import Itasca.Runtime.Compiler.Body.Control.Embedding.OrdinaryEmbedding
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CallbackTables
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredScopes
import Itasca.Runtime.Compiler.Body.Reader.Control.ElseCompilation
import Itasca.Runtime.Compiler.Body.Reader.Control.EndWasm2Compilation
import Itasca.Runtime.Compiler.Body.Reader.Control.RootCompilation
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (),out,after)) :
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 5#u8 before = .ok (.Ok (),out,after)) :
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
      {core := {st.core with pos := next}} data env ctx index .Wasm2 11#u8 before = .ok (.Ok (),out,after)) :
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
