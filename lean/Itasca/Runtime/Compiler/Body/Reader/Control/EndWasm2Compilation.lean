import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixFinish
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.FrontTransitions
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.Return
import Itasca.Runtime.Compiler.Body.Reader.Control.Reachability
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeWasm2
import Itasca.Runtime.Compiler.Body.Reader.Replay.IndexedPreserved

/-!
Sections, each formerly its own module: EndDormantPrefix, EndEnteredPrefix, RootEnd, EndDormantWasm2Prefix, EndWasm2Compilation.
-/

/-! ## EndDormantPrefix -/

section

/-!
A dormant source prefix after the end callback.

Main declarations: `structured_callback_end_dormant_prefix`. A direct consumer is `Compiler.Body.Reader.Control.EndDormantWasm2Prefix`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_end_dormant_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (unentered : current.entered = false) (nonBody : current.form.kind ≠ .Body)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType) (instruction : instr)
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    after.reachable = false ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
        (parent.advance instruction) state.vals.val state.pos.val := by
  have dead : before.reachable = false := by
    cases invariant.mode with
    | live _ entered _ => simp [unentered] at entered
    | terminal dead _ _ => exact dead
    | dormant dead _ => exact dead
  have noGuard : current.guardPosition = none := by
    cases form : current.form <;> simp [SourceScope.guardPosition, form, unentered]
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, patched⟩ := invariant.end_unguarded ops law
    nonBody noGuard state kind bt coordinate sourceBound accepted
  have frameDead := shape.entered.trans unentered
  obtain ⟨noExit, noFixups⟩ := invariant.dormant frame (by simp [framesEq]) frameDead
  have deadAfter : after.reachable = false := by
    cases kindEq : frame.kind <;> simpa [scopeExitLive, dead, noExit, frameDead, kindEq] using reachable
  have codeEq : after.function.code.val = before.function.code.val := by
    simpa [noFixups, patchCode] using patched
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  exact ⟨deadAfter, invariant.close_dormant unentered deadAfter stable maps frame target instruction framesEq
    targetAt codeEq sources consumed (by rw [cursor])⟩
end Itasca.Runtime.Compiler

end

/-! ## EndEnteredPrefix -/

section

/-!
Structured endentered reader prefixes and their complete-profile transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix End Entered -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

theorem structured_callback_end_block_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .block sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.BLOCK sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Block := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_block entered stack stable maps frame target sourceType
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_loop_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype)
    (form : current.form = .loop sourceType)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.LOOP sourceType current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Loop := by simpa [form, ScopeForm.kind] using shape.kind
  obtain ⟨noFixups, noExit⟩ := shape.loopClean sourceType form
  have unchanged : after.function.code.val = before.function.code.val := by simpa [noFixups, patchCode] using codeEq
  have exit : after.reachable = before.reachable := by simpa [scopeExitLive, frameKind, noExit] using reachable
  exact invariant.close_loop entered stack stable maps frame target sourceType framesEq targetAt unchanged form signature
    exit layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_if_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition : U32)
    (form : current.form = .then_ sourceType condition)
    (signature : BlockSignature types sourceType current.params current.results)
    (sameTypes : current.params = current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType current.source [])) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, guard, framesEq, shape, targetAt, guardEq, guardCode, live, codeEq⟩ :=
    invariant.end_guarded ops law sourceType condition form entered state kind bt coordinate sourceBound accepted
  exact invariant.close_if entered stack stable maps frame target sourceType guard condition core.num.U32.MAX
    framesEq guardEq guardCode targetAt codeEq form signature sameTypes live layout sourceTypes sources consumed (by rw [cursor])

theorem structured_callback_end_else_prefix {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (parent current : SourceScope) (raw : List code.StackType) (position : Nat)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns locals (parents ++ [parent]) current raw position)
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (stack : before.reachable = true → Sequence.stackTypes raw = current.front ++ current.results)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (sourceType : blocktype) (condition noEntry : U32) (yes : List instr) (yesExit : Nat) (yesNormal : Bool)
    (form : current.form = .else_ sourceType condition yes yesExit noEntry yesNormal)
    (signature : BlockSignature types sourceType current.params current.results)
    (sourceTypes : SourceStack state.vals.val (current.front ++ current.results))
    (coordinate : before.function.body_start.val + state.pos.val ≤ Usize.max)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val) (consumed : position < state.pos.val)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns locals parents
      (parent.advance (.IFELSE sourceType yes current.source)) state.vals.val state.pos.val := by
  have stable := compiler_end_stable_result ops law before after state kind bt (.Ok ()) accepted
  have maps := compiler_end_map_count ops law before after state kind bt (.Ok ()) accepted
  have sources := compiler_end_sources ops law before after state kind bt accepted
  have cursor := compiler_end_cursor ops law before after state kind bt accepted
  have localLayout := stable.local_layout (invariant.metadata.local_layout initialLocals)
  have layout := compiler_end_layout_success ops law before after state kind bt sourceTypes.concrete localLayout accepted
  rw [sourceTypes.decoded] at layout
  obtain ⟨frame, target, framesEq, shape, targetAt, reachable, codeEq⟩ := invariant.end_unguarded ops law
    (by simp [form, ScopeForm.kind]) (by simp [form, SourceScope.guardPosition]) state kind bt coordinate sourceBound accepted
  have frameKind : frame.kind = .Else := by simpa [form, ScopeForm.kind] using shape.kind
  have exit : after.reachable = (before.reachable || frame.end_reachable) := by
    simpa [scopeExitLive, frameKind] using reachable
  exact invariant.close_else entered stack stable maps frame target sourceType condition noEntry yes yesExit yesNormal
    framesEq targetAt codeEq form signature exit layout sourceTypes sources consumed (by rw [cursor])
end Itasca.Runtime.Compiler

end

/-! ## Structured Reader Prefix End Entered Wasm2 -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_end_entered_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (typesEq : types = env.types.val.map EnvTranslation.funcType)
    (nonRoot : p.current.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm2.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 outer (parent.advance instruction) savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧
      ReaderReachabilityWasm2 after.reachable outer (parent.advance instruction) savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · exact False.elim (nonRoot root)
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
    have outerKnown : ConcreteStack rawOuter := by
      rw [wasm2_spine_values spine]
      simpa only [List.flatMap_def] using savedKnown.current entered
    have erased : code.end_frame st env false = .ok (.Ok (), out) := by
      simp [code.end_frame, read, core.result.Result.Insts.CoreOpsTry.branch]
    have known := wasm2_end_concrete st out env false (p.parents.map Wasm2.Frames.Saved.ctrl)
      (p.parents.map Wasm2.Frames.Saved.bt) p.current.ctrl p.current.bt p.current.ins p.current.outs rawOuter p.current.vals
      ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core outerKnown erased
    have frontEq : current.front = Sequence.stackTypes rawOuter := by
      rw [wasm2_spine_values spine]
      simpa only [List.flatMap_def] using fronts.current
    have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = current.front ++ current.results := by
      intro live
      have segmentKnown : ConcreteStack p.current.vals := (concrete_stack_append.mp (vals ▸ invariant.known live)).2
      have mono := reach.current live
      have realized := results
      rw [mono] at realized
      have segmentTypes := (realized_concrete_types segmentKnown realized).symm
      simp only [vals, Sequence.stackTypes, List.map_append]
      change Sequence.stackTypes rawOuter ++ Sequence.stackTypes p.current.vals = _
      rw [segmentTypes, ← frontEq, same.current.results]
    have effect := code.end_frame.sound st env false
      (p.parents.map Wasm2.Frames.Saved.ctrl) (p.parents.map Wasm2.Frames.Saved.bt)
      p.current.ctrl p.current.bt p.current.ins p.current.outs rawOuter p.current.vals
      ctrls blocks (by simp) vals base header.inputs header.outputs p.opened.shape.core
    rw [erased, WP.spec_ok] at effect
    obtain ⟨allowed, _, positionEq, controls, signatures, values⟩ := effect rfl
    dsimp only at allowed positionEq controls signatures values
    have identity : p.current.form = .then_ → p.current.ins = p.current.outs := by
      intro form
      exact allowed (by simpa [form, Wasm2.Frames.Form.kind] using header.kind)
    have sourceTypes : SourceStack out.core.vals.val (current.front ++ current.results) := by
      refine ⟨known, ?_⟩
      rw [values]
      simp only [savedSplit, List.map_append, List.map_cons, List.map_nil, List.append_eq_nil_iff,
        List.cons_ne_self, and_false, ↓reduceIte]
      simpa [Sequence.stackTypes, List.map_map, Function.comp_def, ← same.current.results] using frontEq.symm
    have signature : BlockSignature types (Wasm2.blockType p.current.bt) current.params current.results := by
      rw [typesEq]
      exact same.current.signature env nonRoot header.inputs header.outputs
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.core.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.core.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals (outer ++ [parent]) current st.core.vals.val p.start.val := sourceSplit ▸ invariant
    have certified : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer
        (parent.advance instruction) out.core.vals.val out.core.pos.val := by
      rcases same.current.close_form closed identity with ⟨form, instructionEq⟩ | ⟨form, instructionEq⟩ |
        ⟨condition, form, instructionEq, sameTypes⟩ | ⟨condition, yes, noEntry, yesExit, yesNormal, form, instructionEq⟩
      · rw [instructionEq]
        exact structured_callback_end_block_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Wasm2.blockType p.current.bt) form signature
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_loop_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Wasm2.blockType p.current.bt) form signature
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_if_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Wasm2.blockType p.current.bt) condition form signature sameTypes
          sourceTypes coordinate sourceBound consumed callback
      · rw [instructionEq]
        exact structured_callback_end_else_prefix ops law initial before after types functions returns compilerLocals
          outer parent current st.core.vals.val p.start.val prefixInv initialLocals entered stack out.core
          p.current.ctrl.kind p.current.bt (Wasm2.blockType p.current.bt) condition noEntry yes yesExit yesNormal form signature
          sourceTypes coordinate sourceBound consumed callback
    have reach' : ReaderReachabilityWasm2 before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed,
      certified, nextSame, reach'.close after.reachable instruction (fun _ => entered), fronts'.pop instruction,
      reader_end_boundary_wasm2 p savedSplit encoded opened afterState, afterState⟩
end Itasca.Runtime.Compiler

end

end

/-! ## RootEnd -/

section

/-!
Reader and validator steps at the function's outermost end.

Main declarations: `reader_end_root_wasm2` and `step_end_root_wasm2`. A direct consumer is `Compiler.Body.Control.Closing.IndexedAdvanceOrClosed`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem reader_end_root_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {kind bt out}
    (single : st.blocks.val.length = 1)
    (read : code.end_frame_info st env false = .ok (.Ok (kind,bt),out)) :
    out.core.ctrls.val = [] := by
  have erased : code.end_frame st env false = .ok (.Ok (),out) := by
    simp [code.end_frame,read,core.result.Result.Insts.CoreOpsTry.branch]
  obtain ⟨C,outer,spine,header,base,typed,controls,blocks,values⟩ := p.opened
  have parents : p.parents = [] := by
    have count := congrArg List.length blocks
    simp only [List.length_append,List.length_map,List.length_singleton] at count
    exact List.eq_nil_of_length_eq_zero (by omega)
  have effect := code.end_frame.sound st env false
    (p.parents.map Wasm2.Frames.Saved.ctrl) (p.parents.map Wasm2.Frames.Saved.bt)
    p.current.ctrl p.current.bt p.current.ins p.current.outs outer p.current.vals
    controls blocks (by simp) values base header.inputs header.outputs p.opened.shape.core
  rw [erased,WP.spec_ok] at effect
  have controlEq := (effect rfl).2.2.2.1
  simpa [parents] using controlEq

theorem step_end_root_wasm2 {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {V} (visitor : code.OpVisitor V)
    (before after : V) (out : code.BodyState) (ctx : code.Context)
    (single : st.blocks.val.length = 1)
    (accepted : code.step_profile visitor st data env ctx index 0x0b#u8 before =
      .ok (.Ok (),out,after)) : out.core.ctrls.val = [] := by
  rw [Wasm2.CallbackTrace.dispatch_end] at accepted
  obtain ⟨pair,read,_⟩ := Wasm2.CallbackTrace.bodyRun.accepted _ _ _ _ _ _ accepted
  exact reader_end_root_wasm2 p single read

end Itasca.Runtime.Compiler

end

/-! ## EndDormantWasm2Prefix -/

section

/-!
Complete-profile transport of a dormant end prefix.

Main declarations: `structured_reader_prefix_end_dormant_wasm2`. A direct consumer is `Compiler.Body.Reader.Control.EndWasm2Compilation`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

private theorem structured_closed_not_body_wasm2 {form bt ops instruction}
    (closed : Wasm2.Frames.Closed form bt ops instruction) : form.kind ≠ .Body := by
  cases closed <;> simp [Wasm2.Frames.Form.kind]

theorem structured_reader_prefix_end_dormant_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env locals index st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.BodyState) (ctx : code.Context)
    (types functions : List functype) (returns compilerLocals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals parents current st.core.vals.val p.start.val)
    (same : ReaderScopeZipperWasm2 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm2 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm2.Frames.Saved.vals))
    (unentered : current.entered = false)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx index 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm2.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      after.reachable = false ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 outer (parent.advance instruction) savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧
      ReaderReachabilityWasm2 after.reachable outer (parent.advance instruction) savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out savedOuter (Wasm2.resumedSource savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · have lengthEq := List.Forall₂.length_eq same.parents
    have sourceEmpty : parents = [] := by simpa [savedEmpty] using lengthEq
    have rootLive := invariant.entryChain.root_entered sourceEmpty
    simp [unentered] at rootLive
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    have nonBody : current.form.kind ≠ .Body := by
      intro body
      have canonical := same.current.form.kind.symm.trans body
      exact structured_closed_not_body_wasm2 closed canonical
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, blocks, vals⟩ := p.opened
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.core.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.core.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefix (jumpTables := jumpTables) emit initial before types functions returns compilerLocals (outer ++ [parent]) current st.core.vals.val p.start.val := sourceSplit ▸ invariant
    obtain ⟨dead, certified⟩ := structured_callback_end_dormant_prefix ops law initial before after types functions returns compilerLocals
      outer parent current st.core.vals.val p.start.val prefixInv unentered nonBody out.core p.current.ctrl.kind
      p.current.bt instruction coordinate sourceBound consumed callback
    have reach' : ReaderReachabilityWasm2 before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed, dead,
      certified, nextSame, reach'.close after.reachable instruction (by simp [dead]), fronts'.pop instruction,
      reader_end_boundary_wasm2 p savedSplit encoded opened afterState, afterState⟩
end Itasca.Runtime.Compiler

end

/-! ## EndWasm2Compilation -/

section

/-!
A non-root END closes the exact retained source scope and restores its parent compiler point, including both entered and omitted subtrees.

Main declarations: `StructuredReaderCompilerStateWasm2.end_nested`. A direct consumer is `Compiler.Body.Control.Table.IndexedTablePointControl`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- A non-root END closes the exact retained source scope and restores its
parent compiler point, including both entered and omitted subtrees. -/
theorem StructuredReaderCompilerStateWasm2.end_nested {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions returns locals data env ctx index ft st parents current savedParents savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions returns locals data env ctx.locals index ft st
      parents current savedParents savedCurrent)
    (initialLocals : LocalLayout initial)
    (typesEq : types = env.types.val.map EnvTranslation.funcType)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (nonRoot : savedCurrent.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[st.core.pos.val]'inbounds = code.OP_END)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index code.OP_END before = .ok (.Ok (), out, after)) :
    StructuredReaderCompilerPointWasm2 jumpTables emit initial after types functions returns locals data env ctx.locals index ft out := by
  let p := state.boundary.pending next advance inbounds
  cases entered : current.entered with
  | true =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_entered_wasm2 p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts state.knownFronts initialLocals entered typesEq nonRoot
        bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, Wasm2.resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
  | false =>
    obtain ⟨outer, parent, savedOuter, savedParent, instruction, split, savedSplit, closed,
      dead, compiled, same, reach, fronts, boundary, afterState⟩ :=
      structured_reader_prefix_end_dormant_wasm2 p ops law initial before after out ctx types functions returns locals
        parents current state.compiled state.sources state.reach state.fronts entered bodyBound
        (by change data.val[st.core.pos.val] = 11#u8; simpa only [code.OP_END] using byte)
        (by simpa only [code.OP_END] using accepted)
    have savedKnown : ReaderKnownFronts (outer ++ [parent]) current
        (savedOuter.map Wasm2.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [split, savedSplit, List.map_append, List.map_cons, List.map_nil] using
        (show ReaderKnownFronts parents current (p.parents.map Wasm2.Frames.Saved.vals) from state.knownFronts)
    exact ⟨outer, parent.advance instruction, savedOuter, Wasm2.resumedSource savedParent p.current instruction,
      compiled, boundary, same, reach, fronts, savedKnown.pop instruction⟩
end Itasca.Runtime.Compiler

end
