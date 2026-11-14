import Itasca.Runtime.Compiler.Local.Callbacks.Control.BranchCallbacks
import Itasca.Runtime.Compiler.Local.Lowering.Control.ReturnContracts
import Itasca.Runtime.Compiler.Local.Lowering.Control.UnreachableContracts
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Relations.Function.FunctionEnvironment
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Function.EnterDead
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: CallbackCursor, CallbackSources, CompilerCallbackMetadata, ScopeCallbackEnter, ScopeCallbackDead, ScopeCallbackIf, CallbackGrowth, CallbackCapacity, CompilerCodeMonotoneCallbacks.
-/

/-! ## CallbackCursor -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_branch_cursor_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → after.next_source = before.next_source := by
  intro success
  subst status
  exact compiler_branch_cursor ops law before after depth skip conditional accepted

theorem compiler_unreachable_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, _, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted).observation
  exact compiler_observe_cursor ops law middle after state (.Ok ()) observed rfl

theorem compiler_return_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, _, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted).observation
  exact compiler_observe_cursor ops law middle after state (.Ok ()) observed rfl

theorem compiler_br_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted).observation
  exact compiler_observe_cursor ops law middle after state (.Ok ()) observed rfl

theorem compiler_br_if_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  obtain ⟨middle, observed⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted).observation
  exact compiler_observe_cursor ops law middle after state (.Ok ()) observed rfl

end Itasca.Runtime.Compiler

end

/-! ## CallbackSources -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_branch_sources_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → SourceProgress before after := by
  intro success
  subst status
  exact compiler_branch_sources ops law before after depth skip conditional accepted

theorem compiler_unreachable_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    SourceProgress before after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_sources ops law before after state (.Ok ()) observed
  | @emitted middle _ _ live emitted observed =>
    exact (compiler_emit_sources ops law before middle .Unreachable emitted).trans
      (compiler_observe_sources ops law {middle with reachable := false} after state (.Ok ()) observed)

theorem compiler_return_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    SourceProgress before after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_sources ops law before after state (.Ok ()) observed
  | @emitted frame source middle _ _ live selected position emitted observed =>
    exact (compiler_emit_sources ops law before middle (.Return source frame.results) emitted).trans
      (compiler_observe_sources ops law {middle with reachable := false} after state (.Ok ()) observed)

theorem compiler_br_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    SourceProgress before after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_sources ops law before after state (.Ok ()) observed
  | @branched middle _ _ live branched observed =>
    exact (compiler_branch_sources ops law before middle depth 0#u32 false branched).trans
      (compiler_observe_sources ops law {middle with reachable := false} after state (.Ok ()) observed)

theorem compiler_br_if_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    SourceProgress before after := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_sources ops law before after state (.Ok ()) observed
  | @branched middle _ _ live branched observed =>
    exact (compiler_branch_sources ops law before middle depth 1#u32 true branched).trans
      (compiler_observe_sources ops law middle after state (.Ok ()) observed)

end Itasca.Runtime.Compiler

end

/-! ## CompilerCallbackMetadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_unreachable_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (status, after)) :
    CompilerStable before after := by
  exact (compiler_unreachable_ordinary_result ops law before after state status accepted).stable

theorem compiler_return_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (status, after)) :
    CompilerStable before after := by
  exact (compiler_return_ordinary_result ops law before after state status accepted).stable

theorem compiler_br_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (status, after)) :
    CompilerStable before after := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types status accepted
  refine ⟨?_, effect.capacity law⟩
  rw [effect.frame]
  rfl

theorem compiler_br_if_stable_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (status, after)) :
    CompilerStable before after := by
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types status accepted
  refine ⟨?_, effect.capacity law⟩
  rw [effect.frame]
  rfl

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackEnter -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful actual BLOCK callback creates its source-aligned frame
and preserves every retained outer frame's physical entry evidence. -/
theorem callback_block_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = true ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after
          (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current])
          (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_block ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
    sourceFits position mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_block after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc true
      paramsWidth resultsWidth (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq])
      (by simpa only [codeEq, position] using Nat.le_refl compiler.function.code.val.length)
    simpa only [position] using fresh
  · exact nested.enter_block parentShape (Itasca.Wasm2.blockType bt) front params results true
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- A successful actual LOOP callback creates its source-aligned frame
and preserves every retained outer frame's physical entry evidence. -/
theorem callback_loop_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++ [.LoopHead] ∧ after.reachable = true ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after
          (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, true, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current])
          (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length true) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_loop ops law compiler state ctrl prior bt signature pc controls selected valuesFit heightFits
    sourceFits position codeFits offsetsFit mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_loop after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc true
      paramsWidth resultsWidth (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq])
      (by simp [codeEq, position])
      (by intro _; simp [codeEq, position])
    simpa only [position] using fresh
  · exact nested.enter_loop parentShape (Itasca.Wasm2.blockType bt) front params results true
  · intro scope frame old
    exact old.extend [.LoopHead] (codeEq) (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackDead -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Dormant BLOCK entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_block_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Block, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Block, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterBlock (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Block bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Block bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_block after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc false
      paramsWidth resultsWidth (by simp) (by simp [mapsEq]) (by simp [codeEq, position])
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_block parentShape (Itasca.Wasm2.blockType bt) front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- Dormant LOOP entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_loop_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Loop, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Loop, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterLoop (Itasca.Wasm2.blockType bt) front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Loop bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_loop after locals front params results (Itasca.Wasm2.blockType bt)
      (alloc.vec.Vec.len compiler.function.controls) height signature.param_slots signature.result_slots pc false
      paramsWidth resultsWidth (by simp) (by simp [mapsEq]) (by simp [codeEq, position]) (by simp)
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_loop parentShape (Itasca.Wasm2.blockType bt) front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

/-- Dormant IF entry pushes its exact physical frame and source
scope while emitting no guard or hook and imposing no live height equation. -/
theorem callback_if_dead_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = false)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops compiler state bt =
      .ok (.Ok (), after)) :
    after.function.code = compiler.function.code ∧ after.reachable = false ∧
      ∃ height source,
        source.val = compiler.function.body_start.val + compiler.next_source.val ∧
        after.frames.val = compiler.frames.val ++
          [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩] ∧
        after.function.controls.val = compiler.function.controls.val ++
          [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
            ctrl.value_stack_base, signature.params, signature.results⟩] ∧
        FrameScope locals after (SourceScope.enterIf (Itasca.Wasm2.blockType bt) 0#u32 front params results compiler.function.code.val.length false)
          ⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
            signature.result_slots, pc, none, false, false, alloc.vec.Vec.new Usize⟩ ∧
        ScopeNesting (parents ++ [current]) (SourceScope.enterIf (Itasca.Wasm2.blockType bt) 0#u32 front params results compiler.function.code.val.length false) ∧
        (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := enter_dead ops law compiler state ctrl prior .Then bt signature pc controls selected
    valuesFit heightFits sourceFits position mapsFit framesFit reachable
  have call : runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt = .ok (.Ok (), after) :=
    accepted
  rw [call, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨codeEq, live, height, source, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨codeEq, live, height, source, sourceEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_if after locals front params results (Itasca.Wasm2.blockType bt)
      0#u32 (alloc.vec.Vec.len compiler.function.controls) (alloc.vec.Vec.len compiler.function.code)
      height signature.param_slots signature.result_slots pc false paramsWidth resultsWidth
      (by simp) (by simp [mapsEq]) (by simpa using position)
      (by simp [codeEq, position]) (by simp)
    simpa only [position, alloc.vec.Vec.len_val, Bool.false_eq_true, ↓reduceIte] using fresh
  · exact nested.enter_if parentShape (Itasca.Wasm2.blockType bt) 0#u32 front params results false
  · intro scope frame old
    exact old.extend [] (by simp only [codeEq, List.append_nil]) (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## ScopeCallbackIf -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- A successful live IF callback retains its actual condition slot and guard,
then pushes the source-aligned THEN frame without changing any outer entry. -/
theorem callback_if_scope {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature) (pc : U32)
    (locals front params results stack : List valtype) (parents : List SourceScope)
    (current : SourceScope) (parentFrame : runtime.compiler.Frame)
    (nested : ScopeNesting parents current) (parentShape : FrameScope locals compiler current parentFrame)
    (localWidth : compiler.function.local_slots.val = slots locals)
    (frontWidth : stackWords (state.vals.val.take ctrl.value_stack_base.val) = slots front)
    (paramsWidth : signature.param_slots.val = slots params)
    (resultsWidth : signature.result_slots.val = slots results)
    (layout : CompilerLayout compiler (stack ++ [.I32]))
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (sourceFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max)
    (position : pc.val = compiler.function.code.val.length + 1)
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max)
    (reachable : compiler.reachable = true)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops compiler state bt =
      .ok (.Ok (), after)) :
    after.reachable = true ∧ ∃ condition height source,
      condition.val = slots (compilerLocals compiler) + slots stack ∧
      source.val = compiler.function.body_start.val + compiler.next_source.val ∧
      after.function.code.val = compiler.function.code.val ++ [.JumpIfZero condition core.num.U32.MAX] ∧
      after.frames.val = compiler.frames.val ++
        [⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
          signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩] ∧
      after.function.controls.val = compiler.function.controls.val ++
        [⟨.Then, source, 0#usize, UScalar.cast .Usize pc, 0#usize,
          ctrl.value_stack_base, signature.params, signature.results⟩] ∧
      FrameScope locals after
        (SourceScope.enterIf (Itasca.Wasm2.blockType bt) condition front params results compiler.function.code.val.length true)
        ⟨alloc.vec.Vec.len compiler.function.controls, .Then, height, signature.param_slots,
          signature.result_slots, pc, some (alloc.vec.Vec.len compiler.function.code), true, false, alloc.vec.Vec.new Usize⟩ ∧
      ScopeNesting (parents ++ [current])
        (SourceScope.enterIf (Itasca.Wasm2.blockType bt) condition front params results compiler.function.code.val.length true) ∧
      (∀ scope frame, FrameScope locals compiler scope frame → FrameScope locals after scope frame) := by
  have effect := callback_if ops law compiler state ctrl prior bt signature pc stack layout codeFits offsetsFit
    controls selected valuesFit heightFits sourceFits position mapsFit framesFit reachable
  rw [accepted, WP.spec_ok] at effect
  dsimp only at effect
  obtain ⟨live, condition, height, source, coordinate, codeEq, heightEq, sourceEq, framesEq, mapsEq⟩ := effect rfl
  refine ⟨live, condition, height, source, coordinate, sourceEq, codeEq, framesEq, mapsEq, ?_, ?_, ?_⟩
  · have fresh := FrameScope.enter_if after locals front params results (Itasca.Wasm2.blockType bt)
      condition (alloc.vec.Vec.len compiler.function.controls) (alloc.vec.Vec.len compiler.function.code)
      height signature.param_slots signature.result_slots pc true paramsWidth resultsWidth
      (by intro _; simpa only [localWidth, frontWidth] using heightEq)
      (by simp [mapsEq]) (by simpa using position) (by simp [codeEq, position])
      (by intro _; simp [codeEq])
    simpa using fresh
  · exact nested.enter_if parentShape (Itasca.Wasm2.blockType bt) condition front params results true
  · intro scope frame old
    exact old.extend [.JumpIfZero condition core.num.U32.MAX] codeEq (by simp [mapsEq])

end Itasca.Runtime.Compiler

end

/-! ## CallbackGrowth -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096


end Itasca.Runtime.Compiler

end

/-! ## CallbackCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096

theorem compiler_branch_capacity_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (depth skip : U32) (conditional : Bool) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops before depth skip conditional = .ok (status, after)) :
    status = .Ok () → capacityMetadata after = capacityMetadata before := by
  intro success
  subst status
  exact compiler_branch_capacity ops law before after depth skip conditional accepted

theorem compiler_unreachable_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted with
  | dead dead observed =>
    have ⟨locals, bound⟩ := compiler_observe_capacity_bound ops law before after state (.Ok ()) observed
    exact ⟨locals, bound rfl⟩
  | @emitted middle _ _ live emitted observed =>
    have preserve := compiler_emit_capacity_metadata ops before middle .Unreachable (.Ok ()) emitted
    have fields : middle.function.local_slots = before.function.local_slots ∧
        middle.function.slot_count = before.function.slot_count := by
      simpa only [capacityMetadata, Prod.mk.injEq] using preserve
    have ⟨locals, bound⟩ := compiler_observe_capacity_bound ops law {middle with reachable := false} after state (.Ok ()) observed
    exact ⟨locals.trans fields.1, by simpa only [fields.1, fields.2] using bound rfl⟩

theorem compiler_return_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted with
  | dead dead observed =>
    have ⟨locals, bound⟩ := compiler_observe_capacity_bound ops law before after state (.Ok ()) observed
    exact ⟨locals, bound rfl⟩
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have preserve := compiler_emit_capacity_metadata ops before middle (.Return source frame.results) (.Ok ()) emitted
    have fields : middle.function.local_slots = before.function.local_slots ∧
        middle.function.slot_count = before.function.slot_count := by
      simpa only [capacityMetadata, Prod.mk.injEq] using preserve
    have ⟨locals, bound⟩ := compiler_observe_capacity_bound ops law {middle with reachable := false} after state (.Ok ()) observed
    exact ⟨locals.trans fields.1, by simpa only [fields.1, fields.2] using bound rfl⟩

theorem compiler_br_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  obtain ⟨middle, observed, slots, locals⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted).observation_slots
  have post := compiler_observe_capacity_bound ops law middle after state (.Ok ()) observed
  exact ⟨post.1.trans locals, by simpa only [slots, locals] using post.2 rfl⟩

theorem compiler_br_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  obtain ⟨middle, observed, slots, locals⟩ := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted).observation_slots
  have post := compiler_observe_capacity_bound ops law middle after state (.Ok ()) observed
  exact ⟨post.1.trans locals, by simpa only [slots, locals] using post.2 rfl⟩

theorem compiler_block_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Block bt accepted

theorem compiler_loop_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Loop bt accepted

theorem compiler_if_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : CapacityStep before after state := by
  exact compiler_enter_capacity ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end

/-! ## CompilerCodeMonotoneCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
theorem compiler_unreachable_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable
      ops before state = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  have code := (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_unreachable.inv ops before after state (.Ok ()) accepted).code law
  rcases code with same | appended
  · rw [same]
  · rw [appended, List.length_append, List.length_singleton]
    omega

theorem compiler_return_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
      ops before state = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return.inv ops before after state (.Ok ()) accepted with
  | dead dead observed =>
    have frame := compiler_observe_frame_raw ops before state (.Ok ()) after observed
    rw [frame]
  | @emitted frame source middle _ _ live selected position emitted observed =>
    have observation := compiler_observe_frame_raw ops {middle with reachable := false} state (.Ok ()) after observed
    have growth := ((runtime.compiler.FunctionCompiler.emit.inv ops before middle _ (.Ok ()) emitted).2 law).1
    rw [observation]
    rcases growth with same | appended
    · rw [same]
    · rw [appended, List.length_append, List.length_singleton]
      omega


theorem compiler_br_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br
      ops before state depth types = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_code_mono ops law before after state (.Ok ()) observed
  | @branched middle _ _ live branched observed =>
    exact (compiler_branch_code_mono ops law before middle depth 0#u32 false (.Ok ()) branched).trans
      (compiler_observe_code_mono ops law {middle with reachable := false} after state (.Ok ()) observed)

theorem compiler_br_if_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState)
    (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if
      ops before state depth types = .ok (.Ok (), after)) :
    before.function.code.val.length ≤ after.function.code.val.length := by
  cases runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if.inv ops before after state depth types (.Ok ()) accepted with
  | dead dead observed => exact compiler_observe_code_mono ops law before after state (.Ok ()) observed
  | @branched middle _ _ live branched observed =>
    exact (compiler_branch_code_mono ops law before middle depth 1#u32 true (.Ok ()) branched).trans
      (compiler_observe_code_mono ops law middle after state (.Ok ()) observed)

theorem compiler_block_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Block bt accepted

theorem compiler_loop_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Loop bt accepted

theorem compiler_if_code_mono {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if
      ops before state bt = .ok (.Ok (), after)) : before.function.code.val.length ≤ after.function.code.val.length := by
  exact compiler_enter_code_mono ops law before after state .Then bt accepted

end Itasca.Runtime.Compiler

end
