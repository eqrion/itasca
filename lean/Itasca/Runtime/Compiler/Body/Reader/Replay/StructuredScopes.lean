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
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterWasm2
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
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchWasm2
import Itasca.Runtime.Compiler.Body.Reader.Replay.Span
import Itasca.Runtime.Compiler.Body.Relations.Control.BranchIfLayout
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchReachable
import Itasca.Runtime.Compiler.Local.Relations.Calls.BranchSuccessConditionalCallbacks
import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredPoint
import Itasca.Runtime.Compiler.Body.Reader.Control.EnterCompilation
import Itasca.Runtime.Compiler.Body.Reader.Control.BranchesCompilation

/-!
Control-scope compilation through a structured reader point.

Main declarations: `StructuredReaderCompilerPointWasm2.scope_step`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca
theorem StructuredReaderCompilerPointWasm2.scope_step {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st}
    (point : StructuredReaderCompilerPointWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (opcode : U8) (supported : ScopeOpcode opcode)
    (byte : data.val[st.core.pos.val]'inbounds = opcode)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 opcode before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  obtain ⟨parents, current, savedParents, savedCurrent, state⟩ := point
  simp only [ScopeOpcode, List.mem_cons, List.not_mem_nil, or_false] at supported
  rcases supported with h | h | h | h | h
  · have op : opcode = 2#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_block ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 3#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, post⟩ := state.enter_loop ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 4#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, post⟩ := state.enter_if ops law next advance inbounds out signatures
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 12#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, post⟩ := state.br ops law next advance inbounds out
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
  · have op : opcode = 13#u8 := by apply UScalar.eq_of_val_eq; exact h
    rw [op] at byte accepted
    obtain ⟨x0, x1, post⟩ := state.br_if ops law next advance inbounds out sourceBound
      (by simpa only [global_simps] using byte) (by simpa only [global_simps] using accepted)
    exact post.point
end Itasca.Runtime.Compiler
