import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndEntered
import Exec.Code.Body.Reader.Common.ReaderEndSignature
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Body.Reader.Common.ReaderKnownFronts
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
