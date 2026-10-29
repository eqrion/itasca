import Itasca.Runtime.Compiler.Body.Reader.Control.EndDormantPrefix
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixCloseLoop
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixCloseIf
import Itasca.Runtime.Compiler.Body.Control.Table.StructuredCompilerPrefixCloseElse
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Reader.Control.EndSignature
import Itasca.Runtime.Compiler.Local.Relations.Control.KnownControlStack
import Itasca.Runtime.Compiler.Body.Reader.Control.ReachabilitySteps
import Itasca.Runtime.Compiler.Body.Reader.Control.ScopeFronts
import Itasca.Runtime.Compiler.Body.Reader.Control.ControlBoundary
import Itasca.Runtime.Compiler.Body.Reader.Control.KnownFronts

/-!
Structured endentered reader prefixes and their complete-profile transport. These are control-map proofs, not Wasm table operations.
-/

/-! ## Structured Reader Prefix End Entered -/

section

namespace Itasca.Runtime.Code
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
end Itasca.Runtime.Code

end

/-! ## Structured Reader Prefix End Entered Wasm2 -/

section

namespace Itasca.Runtime.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_end_entered_wasm2 {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env locals index st}
    (p : Wasm2.Pending data env .Wasm2 locals index st) {A : Type}
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
      st data env ctx index .Wasm2 0x0b#u8 before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm2.Frames.Closed p.current.form p.current.bt p.current.ops instruction ∧
      StructuredCompilerPrefix (jumpTables := jumpTables) emit initial after types functions returns compilerLocals outer (parent.advance instruction) out.core.vals.val out.core.pos.val ∧
      ReaderScopeZipperWasm2 outer (parent.advance instruction) savedOuter (resumedSource savedParent p.current instruction) ∧
      ReaderReachabilityWasm2 after.reachable outer (parent.advance instruction) savedOuter (resumedSource savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm2.Frames.Saved.vals) ∧
      ReaderBoundaryWasm2 data env locals index p.ft out savedOuter (resumedSource savedParent p.current instruction) ∧ p.After out := by
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
      have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ invariant.known live)).2
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
end Itasca.Runtime.Code

end
