import Itasca.Runtime.Compiler.Body.Reader.Replay.StructuredState
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Body.Reader.Control.BlockWasm2Prefix
import Itasca.Runtime.Compiler.Body.Reader.Control.BlockDormantPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFrontEntry
import Itasca.Runtime.Compiler.Body.Reader.Control.IfPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.IfDormantPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.LoopPrefix
import Itasca.Runtime.Compiler.Body.Reader.Control.LoopDormantPrefix

/-!
Structured block, loop and if reader compilation, preserving each control entry shape.
-/

/-! ## Structured Reader Compiler Enter Block -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.enter_block {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_BLOCK)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_BLOCK before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterBlock (Wasm2.blockType bt) front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .block bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_block_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inl rfl)
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterBlock, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterBlock, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_block_dead_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inl rfl)
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterBlock, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterBlock, reach] using entered

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Enter If -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.enter_if {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_IF)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_IF before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front condition, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterIf (Wasm2.blockType bt) condition front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .then_ bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, condition, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, condition, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_if_dead_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, 0#u32, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inr rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterIf, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterIf, reach] using entered

end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Compiler Enter Loop -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem StructuredReaderCompilerStateWasm2.enter_loop {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState)
    (signatures : SignatureSequence initial.signatures.val env.types.val)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_LOOP)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 code.OP_LOOP before = .ok (.Ok (), out, after)) :
    ∃ bt ins outs remaining base front, StructuredReaderCompilerStateWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out
      (parents ++ [current]) (SourceScope.enterLoop (Wasm2.blockType bt) front (ins.map Translate.valueType) (outs.map Translate.valueType) before.function.code.val.length before.reachable)
      (savedParents ++ [{savedCurrent with vals := remaining}]) (Wasm2.Frames.Saved.fresh base .loop bt ins outs) := by
  let p := state.boundary.pending next advance inbounds
  have signaturesBefore : SignatureSequence before.signatures.val env.types.val := by
    simpa only [state.compiled.metadata.fields.1] using signatures
  cases reach : before.reachable with
  | true =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered
  | false =>
    obtain ⟨bt, ins, outs, remaining, base, front, post, compiled, same, reachable, fronts⟩ :=
      structured_reader_prefix_loop_dead_wasm2 p ops law initial before after out ctx
        types functions returns locals parents current state.compiled state.sources state.reach state.fronts reach signaturesBefore byte accepted
    refine ⟨bt, ins, outs, remaining, base, front, compiled, ?_, ?_, reachable, fronts, ?_⟩
    · exact post.boundary (.inr (.inl rfl))
    · exact same
    · apply post.known_fronts state.knownFronts _
      · intro entered
        apply state.reach.current
        simpa only [SourceScope.enterLoop, reach] using entered
      · intro entered
        apply state.compiled.known
        simpa only [SourceScope.enterLoop, reach] using entered

end Itasca.Runtime.Compiler

end
