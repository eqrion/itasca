import Exec.Code.Body.Reader.Table.StructuredReaderPrefixEndEnteredWithTables
import Exec.Code.Body.Reader.Common.ReaderEndSourceWasm1
import Exec.Code.Local.Relations.Control.KnownControlStack
import Exec.Code.Body.Reader.Common.ReaderReachabilitySteps
import Exec.Code.Body.Reader.Control.ReaderScopeFronts
import Exec.Code.Body.Reader.Control.ReaderControlBoundary
import Exec.Code.Body.Reader.Common.ReaderKnownFronts
namespace Exec.Code
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

theorem structured_reader_prefix_end_entered_wasm1_with_tables {jumpTables : List U32} {emit : List valtype → instr → List Bytecode → List valtype → Prop} {data env ctx bodyBt st}
    (p : Wasm1.Pending data env ctx bodyBt st) {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    (initial before after : runtime.compiler.FunctionCompiler A) (out : code.OpIterState)
    (types functions : List functype) (returns locals : List valtype)
    (parents : List SourceScope) (current : SourceScope)
    (invariant : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals parents current st.vals.val p.start.val)
    (same : ReaderScopeZipperWasm1 parents current p.parents p.current)
    (reach : ReaderReachabilityWasm1 before.reachable parents current p.parents p.current)
    (fronts : ReaderScopeFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (savedKnown : ReaderKnownFronts parents current (p.parents.map Wasm1.Frames.Saved.vals))
    (initialLocals : LocalLayout initial) (entered : current.entered = true)
    (nonRoot : p.current.form ≠ .body)
    (bodyBound : before.function.body_start.val + data.length ≤ Usize.max)
    (byte : data.val[p.start.val]'p.inbounds = code.OP_END)
    (accepted : code.step (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      st data env ctx code.OP_END before = .ok (.Ok (), out, after)) :
    ∃ outer parent savedOuter savedParent instruction,
      parents = outer ++ [parent] ∧ p.parents = savedOuter ++ [savedParent] ∧
      Wasm1.Frames.Closed p.current.form p.current.ctrl.block_type p.current.ops instruction ∧
      StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals outer (parent.advance instruction) out.vals.val out.pos.val ∧
      ReaderScopeZipperWasm1 outer (parent.advance instruction) savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧
      ReaderReachabilityWasm1 after.reachable outer (parent.advance instruction) savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧
      ReaderScopeFronts outer (parent.advance instruction) (savedOuter.map Wasm1.Frames.Saved.vals) ∧
      ReaderBoundaryWasm1 data env ctx bodyBt out savedOuter (resumedSourceWasm1 savedParent p.current instruction) ∧ p.After out := by
  obtain ⟨callback, read, encoded, results, zipper, afterState⟩ := reader_end_wasm1 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out byte accepted
  rcases zipper with ⟨root, savedEmpty, _⟩ | ⟨savedOuter, savedParent, instruction, savedSplit, closed, opened⟩
  · exact False.elim (nonRoot root)
  · obtain ⟨outer, parent, sourceSplit, nextSame⟩ := same.close savedOuter savedParent savedSplit instruction
    obtain ⟨C, rawOuter, spine, header, base, typed, ctrls, vals⟩ := p.opened
    have outerKnown : ConcreteStack rawOuter := by
      rw [wasm1_spine_values spine]
      simpa only [List.flatMap_def] using savedKnown.current entered
    have known := wasm1_end_concrete st out _ _ rawOuter p.current.vals p.current.ctrl.kind p.current.ctrl.block_type
      ctrls vals base (Nat.le_of_lt p.val_capacity) outerKnown read
    have frontEq : current.front = Sequence.stackTypes rawOuter := by
      rw [wasm1_spine_values spine]
      simpa only [List.flatMap_def] using fronts.current
    have stack : before.reachable = true → Sequence.stackTypes st.vals.val = current.front ++ current.results := by
      intro live
      have segmentKnown : ConcreteStack p.current.vals := (concreteStack_append.mp (vals ▸ invariant.known live)).2
      have mono := reach.current live
      have realized := results
      rw [mono] at realized
      have segmentTypes := (realized_concrete_types segmentKnown realized).symm
      simp only [vals, Sequence.stackTypes, List.map_append]
      change Sequence.stackTypes rawOuter ++ Sequence.stackTypes p.current.vals = _
      rw [segmentTypes, ← frontEq, same.current.results]
    have sourceTypes : SourceStack out.vals.val (current.front ++ current.results) := by
      refine ⟨known, ?_⟩
      have effect := code.read_end.realizes st (p.parents.map Wasm1.Frames.Saved.ctrl) p.current.ctrl
        rawOuter p.current.vals ctrls vals base (Nat.le_of_lt p.val_capacity)
      rw [read, WP.spec_ok] at effect
      rw [effect.2.2.2.2.1]
      rw [frontEq, same.current.results]
      simp [Sequence.stackTypes, List.map_append, Control.resultTypes, Function.comp_def]
    have sourceBound : p.start.val ≤ limits.MAX_MODULE_BYTES.val := by
      have size := p.size
      have inside := p.inbounds
      change p.start.val < data.val.length at inside
      norm_num [limits.MAX_FUNCTION_BYTES, limits.MAX_MODULE_BYTES] at size ⊢
      omega
    have consumed : p.start.val < out.pos.val := by
      have position := p.pos
      have advanced := afterState.2.1
      omega
    have coordinate : before.function.body_start.val + out.pos.val ≤ Usize.max := by
      have inside := afterState.2.2
      omega
    have prefixInv : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial before types functions returns locals (outer ++ [parent]) current st.vals.val p.start.val := sourceSplit ▸ invariant
    have signature := same.current.signature types
    have certified : StructuredCompilerPrefixWithTables (jumpTables := jumpTables) emit initial after types functions returns locals outer (parent.advance instruction) out.vals.val out.pos.val := by
      rcases same.current.close_form closed with block | loop | then_ | else_
      · obtain ⟨form, rfl⟩ := block
        exact structured_callback_end_block_prefix_with_tables ops law initial before after types functions returns locals
          outer parent current st.vals.val p.start.val prefixInv initialLocals entered stack out
          p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) _ form signature sourceTypes
          coordinate sourceBound consumed callback
      · obtain ⟨form, rfl⟩ := loop
        exact structured_callback_end_loop_prefix_with_tables ops law initial before after types functions returns locals
          outer parent current st.vals.val p.start.val prefixInv initialLocals entered stack out
          p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) _ form signature sourceTypes
          coordinate sourceBound consumed callback
      · obtain ⟨condition, form, rfl, sameTypes⟩ := then_
        exact structured_callback_end_if_prefix_with_tables ops law initial before after types functions returns locals
          outer parent current st.vals.val p.start.val prefixInv initialLocals entered stack out
          p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) _ condition form signature sameTypes sourceTypes
          coordinate sourceBound consumed callback
      · obtain ⟨condition, yes, noEntry, yesExit, yesNormal, form, rfl⟩ := else_
        exact structured_callback_end_else_prefix_with_tables ops law initial before after types functions returns locals
          outer parent current st.vals.val p.start.val prefixInv initialLocals entered stack out
          p.current.ctrl.kind (Control.signature p.current.ctrl.block_type) _ condition noEntry yes yesExit yesNormal form signature sourceTypes
          coordinate sourceBound consumed callback
    have reach' : ReaderReachabilityWasm1 before.reachable (outer ++ [parent]) current
        (savedOuter ++ [savedParent]) p.current := by simpa only [sourceSplit, savedSplit] using reach
    have fronts' : ReaderScopeFronts (outer ++ [parent]) current
        (savedOuter.map Wasm1.Frames.Saved.vals ++ [savedParent.vals]) := by
      simpa only [sourceSplit, savedSplit, List.map_append, List.map_cons, List.map_nil] using fronts
    exact ⟨outer, parent, savedOuter, savedParent, instruction, sourceSplit, savedSplit, closed,
      certified, nextSame, reach'.close after.reachable instruction (fun _ => entered), fronts'.pop instruction,
      reader_end_boundary_wasm1 p savedSplit encoded opened afterState, afterState⟩
end Exec.Code
