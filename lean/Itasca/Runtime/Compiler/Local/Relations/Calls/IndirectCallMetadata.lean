import Itasca.Runtime.Compiler.Local.Relations.Control.BranchSuccessConditional
import Itasca.Runtime.Compiler.Local.Relations.Prefix.ConsumedPrefix
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Runtime.Compiler.Local.Relations.Calls.StatefulCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Metadata.CompilerTerminalMetadata
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic
import Itasca.Runtime.Compiler.Local.Source.SourceCursorTactic
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity

/-!
Sections, each formerly its own module: BranchSuccessCallbacks, BranchSuccessConditionalCallbacks, IndirectCallEmission, IndirectCallEmissionTransport, IndirectCallMetadata.
-/

/-! ## BranchSuccessCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_branch_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_forward_success ops law compiler frame index depth source lookup
      position forward elided sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_pos elided]
      exact ⟨site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_forward_success ops law compiler frame index depth source lookup
      position forward nonempty different sourcePosition after accepted
    obtain ⟨code, fixups, site, position, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [BranchHole, if_neg elided]
      exact ⟨by simp [code], site, by simp [appended], position, by simp [code, core.num.U32.MAX, U32.rMax]⟩
    · simpa [branchInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using position, appended⟩


theorem callback_branch_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType = .ok (.Ok (), after)) : after.reachable = false ∧ ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        BranchHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results ∧
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.results core.num.U32.MAX ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 1) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_forward_success ops law compiler frame index depth source lookup position forward
      sourcePosition changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law { changed with reachable := false } state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨fixups, frames, hole, code, site⟩ := effect
    exact ⟨hr, fixups, by simpa [hframes] using frames, by simpa [hcode] using hole,
      by simpa [hcode] using code, site⟩

theorem compiler_branch_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 0#u32 false = .ok (.Ok (), after)) :
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        after.frames = compiler.frames := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · have effect := branch_elided_loop_success ops law compiler frame index depth source lookup
      position kind elided sourcePosition after accepted
    simpa [branchInstructions, elided] using effect
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_transfer_loop_success ops law compiler frame index depth source lookup
      position kind nonempty different sourcePosition after accepted
    simpa [branchInstructions, elided] using effect


theorem callback_branch_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val = compiler.height.val)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops compiler state depth resultType = .ok (.Ok (), after)) : after.reachable = false ∧
        after.function.code.val = compiler.function.code.val ++
          branchInstructions frame.height source frame.params frame.start_pc ∧
        after.frames = compiler.frames := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_loop_success ops law compiler frame index depth source lookup position kind
      sourcePosition changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law { changed with reachable := false } state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨code, frames⟩ := effect
    exact ⟨hr, by simpa [hcode] using code, by simpa [hframes] using frames⟩

end Itasca.Runtime.Compiler

end

/-! ## BranchSuccessConditionalCallbacks -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
theorem compiler_branch_if_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.results = 0#u32 ∨ source = frame.height then 1 else 3))
    (fixupsBefore : ∀ site, site ∈ frame.fixups.val → site.val < compiler.function.code.val.length)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        after.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  by_cases elided : frame.results = 0#u32 ∨ source = frame.height
  · have effect := branch_if_elided_forward_success ops law compiler frame index depth source condition lookup
      position forward elided sourcePosition conditionAt after accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [ConditionalHole, if_pos elided]
      exact ⟨site, by simp [appended], sitePosition, by simp [code], by simpa [elided] using resumePosition⟩
    · simpa [branchIfInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using sitePosition, appended⟩
  · have nonempty : frame.results ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_if_transfer_forward_success ops law compiler frame index depth source condition resume lookup
      position forward nonempty different sourcePosition conditionAt (by simpa [elided] using resumePosition)
      after accepted
    obtain ⟨code, fixups, site, sitePosition, frames, appended⟩ := effect
    refine ⟨fixups, frames, ?_, ?_, ?_⟩
    · simp only [ConditionalHole, if_neg elided]
      refine ⟨by simp [code], ?_, by simp [code], site, by simp [appended], sitePosition,
        by simp [code], by simpa [elided] using resumePosition⟩
      intro old member
      simp only [appended, List.mem_append, List.mem_singleton] at member
      rcases member with prior | rfl
      · have bound := fixupsBefore old prior
        omega
      · omega
    · simpa [branchIfInstructions, elided] using code
    · exact ⟨site, by simpa [elided] using sitePosition, appended⟩


theorem compiler_branch_if_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.params = 0#u32 ∨ source = frame.height then 1 else 3))
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.control.FunctionCompiler.branch ops compiler depth 1#u32 true = .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++
      branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
    after.frames = compiler.frames := by
  by_cases elided : frame.params = 0#u32 ∨ source = frame.height
  · have effect := branch_if_elided_loop_success ops law compiler frame index depth source condition lookup
      position kind elided sourcePosition conditionAt after accepted
    simpa [branchIfInstructions, elided] using effect
  · have nonempty : frame.params ≠ 0#u32 := fun eq => elided (Or.inl eq)
    have different : source ≠ frame.height := fun eq => elided (Or.inr eq)
    have effect := branch_if_transfer_loop_success ops law compiler frame index depth source condition resume lookup
      position kind nonempty different sourcePosition conditionAt (by simpa [elided] using resumePosition) after accepted
    simpa [branchIfInstructions, elided] using effect

theorem callback_branch_if_forward_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (forward : frame.kind ≠ .Loop)
    (sourcePosition : source.val + frame.results.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.results = 0#u32 ∨ source = frame.height then 1 else 3))
    (fixupsBefore : ∀ site, site ∈ frame.fixups.val → site.val < compiler.function.code.val.length)
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType = .ok (.Ok (), after)) : ∃ fixups,
        after.frames.val = compiler.frames.val.set index.val { frame with end_reachable := true, fixups } ∧
        ConditionalHole after.function.code.val fixups.val compiler.function.code.val.length
          frame.height source frame.results condition resume ∧
        after.function.code.val = compiler.function.code.val ++
          branchIfInstructions frame.height source frame.results core.num.U32.MAX condition resume ∧
        ∃ site, site.val = compiler.function.code.val.length +
          (if frame.results = 0#u32 ∨ source = frame.height then 0 else 2) ∧
          fixups.val = frame.fixups.val ++ [site] := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_if_forward_success ops law compiler frame index depth source condition resume
      lookup position forward sourcePosition conditionAt resumePosition fixupsBefore changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law changed state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨fixups, frames, hole, code, site⟩ := effect
    exact ⟨fixups, by simpa [hframes] using frames, by simpa [hcode] using hole,
      by simpa [hcode] using code, site⟩

theorem callback_branch_if_loop_success {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (resultType : Itasca.signature.ResultType)
    (reachable : compiler.reachable = true)
    (frame : runtime.compiler.Frame) (index : Usize) (depth source condition resume : U32)
    (lookup : compiler.frames.val[index.val]? = some frame)
    (position : index.val + depth.val + 1 = compiler.frames.val.length)
    (kind : frame.kind = .Loop)
    (sourcePosition : source.val + frame.params.val + 1 = compiler.height.val)
    (conditionAt : compiler.before.val[compiler.before.val.length - 1]? = some condition)
    (resumePosition : resume.val = compiler.function.code.val.length +
      (if frame.params = 0#u32 ∨ source = frame.height then 1 else 3))
    (after : runtime.compiler.FunctionCompiler A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops compiler state depth resultType = .ok (.Ok (), after)) :
    after.function.code.val = compiler.function.code.val ++
      branchIfInstructions frame.height source frame.params frame.start_pc condition resume ∧
    after.frames = compiler.frames := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if at accepted
  rw [if_pos reachable] at accepted
  obtain ⟨⟨result, changed⟩, branchCall, rest⟩ := bind_ok_inv _ _ _ accepted
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] at rest
  | Ok value =>
    cases value
    have effect := compiler_branch_if_loop_success ops law compiler frame index depth source condition resume
      lookup position kind sourcePosition conditionAt resumePosition changed branchCall
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    have observed := compiler_observe ops law changed state
    rw [rest, WP.spec_ok] at observed
    dsimp only at observed
    obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed rfl
    obtain ⟨code, frames⟩ := effect
    exact ⟨by simpa [hcode] using code, by simpa [hframes] using frames⟩

end Itasca.Runtime.Compiler

end

/-! ## IndirectCallEmission -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- An indirect call retains both source indices and the actual function-local
pair entry. The table selector follows the full parameter word region. -/
inductive IndirectCallEmission (pairs : List (U32 × U32)) (C : context) :
    List valtype → instr → List Bytecode → List valtype → Prop where
  | call (front params results : List valtype) (typeIndex tableIndex entry index base : U32)
      (bounds : limits)
      (signature : C.TYPES[typeIndex.val]? = some ⟨.mk_list params,.mk_list results⟩)
      (table : C.TABLES[tableIndex.val]? = some (.mk_tabletype bounds .FUNCREF))
      (pair : pairs[entry.val]? = some (tableIndex,typeIndex))
      (basePosition : base.val = slots C.LOCALS + slots front)
      (indexPosition : index.val = base.val + slots params) :
      IndirectCallEmission pairs C ((front ++ params) ++ [.I32])
        (.CALL_INDIRECT (.mk_uN tableIndex.val) (.mk_uN typeIndex.val))
        [.CallIndirect entry index base] (front ++ results)

theorem IndirectCallEmission.append_pairs {pairs C before instruction emitted after}
    (emission : IndirectCallEmission pairs C before instruction emitted after)
    (extra : List (U32 × U32)) :
    IndirectCallEmission (pairs ++ extra) C before instruction emitted after := by
  cases emission with
  | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
    apply IndirectCallEmission.call front params results typeIndex tableIndex entry index base bounds signature table
      _ basePosition indexPosition
    have bound := (List.getElem?_eq_some_iff.mp pair).1
    simpa [List.getElem?_append,bound] using pair
end Itasca.Runtime.Compiler

end

/-! ## IndirectCallEmissionTransport -/

section

namespace Itasca.Runtime.Compiler
open Aeneas.Std

theorem IndirectCallEmission.context {pairs C D before instruction emitted after}
    (types : D.TYPES = C.TYPES) (locals : D.LOCALS = C.LOCALS) (tables : D.TABLES = C.TABLES)
    (emission : IndirectCallEmission pairs C before instruction emitted after) :
    IndirectCallEmission pairs D before instruction emitted after := by
  cases emission with
  | call front params results typeIndex tableIndex entry index base bounds signature table pair basePosition indexPosition =>
    exact .call front params results typeIndex tableIndex entry index base bounds
      (by simpa only [types] using signature) (by simpa only [tables] using table) pair
      (by simpa only [locals] using basePosition) indexPosition
end Itasca.Runtime.Compiler

end

/-! ## IndirectCallMetadata -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
theorem compiler_indirect_call_ordinary_result {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (status, after)) :
    CompilerOrdinaryStable before after := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    simp only [indirectCallLowering] at accepted
    all_goals repeat' metadata_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_ordinary_result ops law before after state status accepted

theorem compiler_indirect_call_sources {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (), after)) :
    SourceProgress before after := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    simp only [indirectCallLowering] at accepted
    all_goals repeat' sources_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_sources ops law before after state (.Ok ()) accepted

theorem compiler_indirect_call_cursor {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (), after)) :
    after.next_source = state.pos := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    simp only [indirectCallLowering] at accepted
    all_goals repeat' cursor_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact compiler_observe_cursor ops law before after state (.Ok ()) accepted rfl

theorem compiler_indirect_call_capacity {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (a b : U32)
    (accepted : runtime.compiler.lower.FunctionCompiler.op ops before state 17#u16 a b 0#u128 = .ok (.Ok (), after)) :
    CapacityStep before after state := by
  by_cases reach : before.reachable = true
  · rw [lower_indirect_call_dispatch ops before state a b reach] at accepted
    simp only [indirectCallLowering] at accepted
    all_goals repeat' capacity_step accepted using ops, law
  · unfold runtime.compiler.lower.FunctionCompiler.op at accepted
    rw [if_neg reach] at accepted
    exact ⟨(compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).1,
      (compiler_observe_capacity_bound ops law before after state (.Ok ()) accepted).2 rfl⟩

end Itasca.Runtime.Compiler

end
