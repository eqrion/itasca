import Itasca.Runtime.Compiler.Body.Reader.Control.StructuredRootMapPublication
import Itasca.Runtime.Compiler.Local.Checking.RootCloseInstructionPrefix
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
import Itasca.Runtime.Compiler.Body.Source.TypedLowering
import Itasca.Runtime.Compiler.Body.Reader.Control.RootCompilation
import Itasca.Runtime.Compiler.Local.Checking.FrameExitSlotBounds

/-!
Structured compiler root closure checked instructions and their reader-step lift. The source-prefix argument establishes the concrete reader preservation theorem.
-/

/-! ## Structured Root Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Source root geometry, the preceding live stack, and branch exits discharge every
stored instruction check at actual function close. The final return's capacity
comes from the retained slot bounds and prepared local region. -/
theorem structured_root_checked_instructions {jumpTables : List U32}
    {emit : List valtype → instr → List Bytecode → List valtype → Prop} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {types functions returns locals current raw position}
    (invariant : StructuredCompilerPrefix jumpTables emit initial before types functions returns locals [] current raw position)
    (rootForm : current.form = .body) (entered : current.entered = true)
    (front : current.front = []) (results : current.results = returns)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (sourceBound : position ≤ limits.MAX_MODULE_BYTES.val)
    (state : code.OpIterState) (kind : code.LabelKind) (bt : signature.BlockType)
    (normal : before.reachable = true → Sequence.stackTypes raw = returns)
    (exits : ∀ frame ∈ before.frames.val, frame.end_reachable = true →
      frame.height.val+frame.results.val ≤ before.function.slot_count.val)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (consumed : position < state.pos.val)
    (endBound : before.function.body_start.val+state.pos.val ≤ before.function.body_end.val)
    (called : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (),after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  obtain ⟨prior,frame,frames,paired,shape⟩ := invariant.frames.split
  have empty : prior = [] := by cases paired; rfl
  let rest := alloc.vec.Vec.new runtime.compiler.Frame
  have restEmpty : rest.val = [] := by simp [rest,alloc.vec.Vec.new]
  have physical : before.frames.val = rest.val++[frame] := by simpa only [restEmpty,empty] using frames
  have root : frame.kind = .Body := by simpa only [rootForm,ScopeForm.kind] using shape.kind
  have noIf : frame.if_pc = none := by
    have guard := shape.guard
    simpa only [rootForm,SourceScope.guardPosition,Option.map_eq_none_iff] using guard
  have bound := invariant.codeBudget.fetch_bound sourceBound
  let target : U32 := UScalar.ofNatCore before.function.code.val.length (by scalar_tac)
  have sites := (invariant.mode.sites frame (by simp [frames])).branches.branches
  let geometry : ScopeCloseGeometry before := ⟨frame,rest,target,physical,rfl,sites⟩
  have stable := invariant.metadata.trans (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called)
  have localLayout := stable.local_layout initialLayout
  obtain ⟨_,_,_,_,localsEq,_,slotsEq,_⟩ := stable.fields
  have localTypes : compilerLocals after = locals := by simpa only [compilerLocals,localsEq] using initialLocals
  have localCapacity : after.function.local_slots.val ≤ after.function.slot_count.val := by
    rw [slotsEq]
    exact initialCapacity.trans stable.capacity
  have height : frame.height = after.function.local_slots := by
    apply UScalar.eq_of_val_eq
    rw [localLayout.slots,localTypes]
    simpa only [front,slots,Nat.add_zero] using shape.height entered
  have width : frame.results.val = slots returns := by simpa only [results] using shape.results
  obtain ⟨codeFits,offsetsFit,_,_⟩ := invariant.capacities sourceBound
  have progress : before.next_source.val < state.pos.val := lt_of_le_of_lt invariant.cursor consumed
  have endFits : before.function.body_end.val ≤ Usize.max := by scalar_tac
  have returnFits : frame.height.val+
      (if scopeExitLive before.reachable frame then frame.results else 0#u32).val ≤ after.function.slot_count.val := by
    have capacity := (compiler_end_stable_result ops law before after state kind bt (.Ok ()) called).capacity
    by_cases live : before.reachable = true
    · have layout := (invariant.live live).2.layout
      have bound := layout.live_slots_fit live
      have localsMatch := (invariant.live live).2.localsEq
      rw [normal live,localsMatch,← width] at bound
      have heightBefore : frame.height.val = slots locals := by
        simpa only [front,slots,Nat.add_zero] using shape.height entered
      rw [← heightBefore] at bound
      simpa [scopeExitLive,live,root] using bound.trans capacity
    · have dead : before.reachable = false := by cases reachable : before.reachable <;> simp_all
      by_cases exit : frame.end_reachable = true
      · have bound := exits frame (by simp [frames]) exit
        simpa [scopeExitLive,dead,root,exit] using bound.trans capacity
      · have noExit : frame.end_reachable = false := by cases reachable : frame.end_reachable <;> simp_all
        simpa [scopeExitLive,dead,root,noExit,height] using localCapacity
  refine ⟨compiler_root_close_checked_instructions_of_slots ops law before after state kind bt geometry root restEmpty noIf
    codeFits offsetsFit (by omega) (by omega) maps held returnFits called,?_⟩
  have effect := close_function_effect ops law before state frame rest target physical root noIf rfl sites shape.mapBound
    (by omega) codeFits offsetsFit (by omega)
  have canonical : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state .Block .Empty =
      .ok (.Ok (),after) := called
  rw [canonical,WP.spec_ok] at effect
  obtain ⟨frames,_,_,_⟩ := effect rfl
  rw [frames]
  exact restEmpty

end Itasca.Runtime.Compiler

end

/-! ## Reader Root Instruction Prefix -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

/-- Actual root END checks every stored instruction from its typed preceding stack and retained exits. -/
theorem StructuredReaderCompilerStateWasm2.root_checked_instructions {jumpTables : List U32} {A : Type}
    (ops : runtime.platform.Alloc A) (law : Platform.AllocCorrect ops)
    {initial before after : runtime.compiler.FunctionCompiler A}
    {emit types functions locals data env ctx index ft st current savedCurrent}
    (state : StructuredReaderCompilerStateWasm2 jumpTables emit initial before types functions (ft.results.val.map Translate.valueType) locals
      data env ctx.locals index ft st [] current [] savedCurrent)
    (root : savedCurrent.form = .body)
    (next : Usize) (advance : next.val = st.core.pos.val + 1) (inbounds : st.core.pos.val < data.length)
    (out : code.BodyState) (sourceBound : data.length ≤ limits.MAX_MODULE_BYTES.val)
    (bodyExtent : before.function.body_end.val = before.function.body_start.val+data.length)
    (initialLayout : LocalLayout initial) (initialLocals : compilerLocals initial = locals)
    (initialCapacity : initial.function.local_slots.val ≤ initial.function.slot_count.val)
    (maps : ControlMapPublication before) (held : CompilerInstructionPrefix before)
    (exits : FrameExitSlotBounds before)
    (byte : data.val[st.core.pos.val]'inbounds = 0x0b#u8)
    (accepted : code.step_profile (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops)
      {core := {st.core with pos := next}} data env ctx index .Wasm2 0x0b#u8 before = .ok (.Ok (), out, after)) :
    CheckedInstructionPrefix after.function ∧ after.frames.val = [] := by
  let p := state.boundary.pending next advance inbounds
  obtain ⟨callback, read, encoded, realizes, zipper, afterState⟩ := reader_end_wasm2 p
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor ops) before after out ctx byte accepted
  obtain ⟨C, outer, spine, header, base, typed, controls, blocks, vals⟩ := state.boundary.opened
  have outerEq : outer = [] := by simpa using wasm2_spine_values spine
  have rawEq : st.core.vals.val = savedCurrent.vals := by simpa [outerEq] using vals
  have savedType : savedCurrent.bt = .TypeIndex index := by
    simpa [Wasm2.Frames.bodyType] using state.boundary.bodyType
  have outs : savedCurrent.outs = ft.results.val := by
    have outputs := header.outputs
    simpa [savedType, Wasm2.outputs, Wasm2.resolve, state.boundary.signature] using outputs.symm
  have sourceForm : current.form = .body := by
    have matching := state.sources.current.form
    generalize formEq : current.form = f at matching
    rw [root] at matching
    cases matching
    rfl
  have front : current.front = [] := by simpa [Sequence.stackTypes] using state.fronts.current
  have params : current.params = [] := by simpa [root, Wasm2.Frames.Form.params] using state.sources.current.params
  have results : current.results = ft.results.val.map Translate.valueType := by simpa [outs] using state.sources.current.results
  have stack : before.reachable = true → Sequence.stackTypes st.core.vals.val = ft.results.val.map Translate.valueType := by
    intro live
    have concrete : ConcreteStack savedCurrent.vals := rawEq ▸ (state.compiled.known live)
    have mono := state.reach.current live
    have actual : Sequence.Realizes false savedCurrent.vals (savedCurrent.outs.map Translate.valueType) := by
      simpa [p, ReaderBoundaryWasm2.pending, mono] using realizes
    have decoded := realized_concrete_types concrete actual
    simpa [rawEq, outs] using decoded.symm
  have consumed : st.core.pos.val < out.core.pos.val := encoded.span.1
  have endBound : before.function.body_start.val+out.core.pos.val ≤ before.function.body_end.val := by
    have bounded := afterState.2.2
    rw [bodyExtent]
    exact Nat.add_le_add_left bounded _
  have entry := state.compiled.entryChain.root_entered rfl
  exact structured_root_checked_instructions ops law state.compiled sourceForm entry front results
    initialLayout initialLocals initialCapacity ((Nat.le_of_lt inbounds).trans sourceBound)
    out.core savedCurrent.ctrl.kind savedCurrent.bt stack exits maps held consumed endBound callback

end Itasca.Runtime.Compiler

end
