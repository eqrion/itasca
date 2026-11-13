import Itasca.Runtime.Compiler.Local.Callbacks.Effects.OrdinaryEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameStart
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CallbackTables
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchControl
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservation
import Itasca.Runtime.Compiler.Local.Callbacks.Fixups.FixupBudget
import Itasca.Runtime.Compiler.Local.Relations.Control.BranchCertificates
import Itasca.Runtime.Compiler.Local.Callbacks.Function.CloseFunction

/-!
Sections, each formerly its own module: ControlEffects, ElseSafety, CloseMapEffect.
-/

/-! ## ControlEffects -/

section

/-!
What every structured-control compiler callback preserves: the function
tables, the branch-table depths, emitted code, the fixup budget, and slot
capacity.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca

structure ControlEffects {A : Type} (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) : Prop where
  tables : CompilerTables.ofFunction after.function = CompilerTables.ofFunction before.function
  depths : after.table_depths = before.table_depths
  code_mono : before.function.code.val.length ≤ after.function.code.val.length
  fixups : FixupBudget before.frames.val before.function.code.val.length →
    FixupBudget after.frames.val after.function.code.val.length
  capacity : CapacityStep before after state

theorem ControlEffects.auxiliary_growth {A : Type} {before after : runtime.compiler.FunctionCompiler A}
    {state : Itasca.code.OpIterState} (effects : ControlEffects before after state) :
    AuxiliaryGrowth before after :=
  .of_tables effects.tables effects.code_mono

theorem compiler_block_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_block ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_block_tables ops law before after state bt accepted,
    compiler_block_depths ops law before after state bt accepted,
    compiler_block_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Block bt budget accepted,
    compiler_block_capacity ops law before after state bt accepted⟩

theorem compiler_loop_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_loop ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_loop_tables ops law before after state bt accepted,
    compiler_loop_depths ops law before after state bt accepted,
    compiler_loop_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Loop bt budget accepted,
    compiler_loop_capacity ops law before after state bt accepted⟩

theorem compiler_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_if ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_if_tables ops law before after state bt accepted,
    compiler_if_depths ops law before after state bt accepted,
    compiler_if_code_mono ops law before after state bt accepted,
    fun budget => compiler_enter_fixup_budget ops law before after state .Then bt budget accepted,
    compiler_if_capacity ops law before after state bt accepted⟩

theorem compiler_else_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops before state bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_else_tables ops law before after state bt accepted,
    compiler_else_depths ops law before after state bt accepted,
    compiler_else_code_mono ops law before after state bt accepted,
    fun budget => compiler_else_fixup_budget ops law before after state bt budget accepted,
    compiler_else_capacity ops law before after state bt accepted⟩

theorem compiler_end_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (kind : Itasca.code.LabelKind) (bt : Itasca.signature.BlockType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops before state kind bt = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_end_tables ops law before after state kind bt accepted,
    compiler_end_depths ops law before after state kind bt accepted,
    compiler_end_code_mono ops law before after state kind bt accepted,
    fun budget => compiler_end_fixup_budget ops law before after state kind bt budget accepted,
    compiler_end_capacity ops law before after state kind bt accepted⟩

theorem compiler_br_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br ops before state depth types = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_br_tables ops law before after state depth types accepted,
    compiler_br_depths ops law before after state depth types accepted,
    compiler_br_code_mono ops law before after state depth types accepted,
    fun budget => compiler_br_fixup_budget ops law before after state depth types budget accepted,
    compiler_br_capacity ops law before after state depth types accepted⟩

theorem compiler_br_if_effects {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (depth : U32) (types : Itasca.signature.ResultType)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_br_if ops before state depth types = .ok (.Ok (), after)) :
    ControlEffects before after state :=
  ⟨compiler_br_if_tables ops law before after state depth types accepted,
    compiler_br_if_depths ops law before after state depth types accepted,
    compiler_br_if_code_mono ops law before after state depth types accepted,
    fun budget => compiler_br_if_fixup_budget ops law before after state depth types budget accepted,
    compiler_br_if_capacity ops law before after state depth types accepted⟩

end Itasca.Runtime.Compiler

end

/-! ## ElseSafety -/

section

/-! The actual ELSE callback preserves source control metadata, records the
then-arm skip when needed, and retargets the original condition to the start
of the else arm. Unentered and non-fallthrough arms are handled explicitly. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_else_live_raw {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition old target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = true) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length + 1)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code.val = (compiler.function.code.val ++ [runtime.bytecode.Instr.Jump core.num.U32.MAX]).set guard.val
          (.JumpIfZero condition target) ∧
        ∃ fixups, fixups.val = frame.fixups.val ++ [alloc.vec.Vec.len compiler.function.code] ∧
          out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none, end_reachable := true, fixups }] ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, ite_true, Bool.or_true]
  step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code)
    fixupsFit as ⟨result, budget, fixups, pushed⟩
  rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_emit ops law
      { compiler with frames := back { frame with kind := .Else, if_pc := none, end_reachable := true, fixups }, reachable := frame.entry_reachable }
      (.Jump core.num.U32.MAX) codeFits offsetsFit coordinateFits as ⟨result, emitted, effect⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      obtain ⟨budget, code, offsets, emittedEq, codeAppend, offsetAppend⟩ := effect rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [compiler_pc_eq ops emitted target (by simpa [emittedEq, codeAppend] using position)]
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have guardBound := (List.getElem?_eq_some_iff.mp guardCode).1
      have retained : emitted.function.code.val[guard.val]? = some (.JumpIfZero condition old) := by
        simp only [emittedEq, codeAppend]
        rw [List.getElem?_append_left guardBound]
        exact guardCode
      step with compiler_patch ops emitted guard (.zero condition) old target retained
        as ⟨status, patched, statusEq, patchedEffect⟩
      subst status
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      obtain ⟨newCode, patchedEq, codeSet⟩ := patchedEffect
      step with compiler_observe ops law patched state as ⟨out, observed, accepted⟩
      obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
      refine ⟨?_, ?_, fixups, appended, ?_⟩
      · simpa [patchedEq, emittedEq] using hr
      · simpa [hcode, patchedEq, emittedEq, codeAppend, BranchKind.instruction] using codeSet
      · simp [hframes, patchedEq, emittedEq, backEq, alloc.vec.Vec.set_val_eq, atLast, frames]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- When the then arm does not fall through, ELSE emits no skip instruction;
it still retargets the initial conditional guard and restores entry reachability. -/
@[step] theorem compiler_else_dead_raw {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (guard : Usize) (condition old target : U32)
    (frames : compiler.frames.val = prior ++ [frame])
    (reachable : compiler.reachable = false) (guardPc : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → out.2.reachable = frame.entry_reachable ∧
        out.2.function.code.val = compiler.function.code.val.set guard.val (.JumpIfZero condition target) ∧
        out.2.frames.val = prior ++ [{ frame with kind := .Else, if_pc := none }] ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, guardPc, reachable, Bool.false_eq_true, ite_false, Bool.or_false]
  let updated := { compiler with frames := back { frame with kind := .Else, if_pc := none }, reachable := frame.entry_reachable }
  rw [compiler_pc_eq ops updated target position]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with compiler_patch ops updated guard (.zero condition) old target guardCode
    as ⟨status, patched, statusEq, patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨newCode, patchedEq, codeSet⟩ := patchedEffect
  step with compiler_observe ops law patched state as ⟨out, observed, accepted⟩
  obtain ⟨hoff, hh, hl, hls, hlo, hr, hcode, hsources, hnext, hcap, hmono, hframes, hcontrols⟩ := observed accepted
  refine ⟨?_, ?_, ?_⟩
  · simpa [patchedEq, updated] using hr
  · simpa [hcode, patchedEq, updated, BranchKind.instruction] using codeSet
  · simp [hframes, patchedEq, updated, backEq, alloc.vec.Vec.set_val_eq, atLast, frames]

private theorem else_live_no_guard {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (live : compiler.reachable = true) (noGuard : frame.if_pc = none)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ _ => True ⦄ := by
  have nonempty : compiler.frames.val.isEmpty = false := by simp [frames]
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else
  simp only [alloc.vec.Vec.is_empty, bind_ok, nonempty, Bool.false_eq_true, ite_false]
  step as ⟨index, indexEq⟩
  have atLast : index.val = prior.length := by simp [frames, alloc.vec.Vec.len] at indexEq; omega
  step as ⟨found, back, foundEq, backEq⟩
  have same : found = frame := by simpa [atLast, frames] using foundEq
  rw [same]
  simp only [core.option.Option.take, noGuard, live, ite_true, Bool.or_true]
  step with budget_push ops law compiler.budget frame.fixups (alloc.vec.Vec.len compiler.function.code)
    fixupsFit as ⟨result, budget, fixups, pushed⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_emit ops law
      { compiler with budget := budget, frames := back { frame with kind := .Else, if_pc := none, end_reachable := true, fixups }, reachable := frame.entry_reachable }
      (.Jump core.num.U32.MAX) codeFits offsetsFit coordinateFits as ⟨result, emitted, effect⟩
    cases result with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact WP.spec_mono (compiler_observe_stack ops law emitted state) (by simp)

@[step] theorem compiler_else_total {A} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (bt : Itasca.signature.BlockType)
    (frame : runtime.compiler.Frame) (prior : List runtime.compiler.Frame)
    (frames : compiler.frames.val = prior ++ [frame])
    (sites : FrameSites compiler.function.code.val frame)
    (fixupsFit : frame.fixups.val.length < Usize.max)
    (pcBound : compiler.function.code.val.length + 1 < 2^32)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (offsetsFit : compiler.function.source_offsets.val.length < Usize.max)
    (coordinateFits : compiler.function.body_start.val + compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ out =>
      out.1 = .Ok () → ObservedStack out.2 state.vals.val ⦄ := by
  have total : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else ops compiler state bt ⦃ _ => True ⦄ := by
    by_cases live : compiler.reachable = true
    · cases guardEq : frame.if_pc with
      | none =>
        exact else_live_no_guard ops law compiler state bt frame prior frames live guardEq
          fixupsFit codeFits offsetsFit coordinateFits
      | some guard =>
        obtain ⟨condition, old, found⟩ := sites.guard guard guardEq
        let target : U32 := UScalar.ofNatCore (compiler.function.code.val.length + 1) pcBound
        exact WP.spec_mono (compiler_else_live_raw ops law compiler state bt frame prior guard condition old target
          frames live guardEq found rfl fixupsFit codeFits offsetsFit coordinateFits) (by simp)
    · have dead : compiler.reachable = false := by simpa using live
      cases guardEq : frame.if_pc with
      | none => exact WP.spec_mono (compiler_else_unentered ops law compiler state bt frame prior frames dead guardEq) (by simp)
      | some guard =>
        obtain ⟨condition, old, found⟩ := sites.guard guard guardEq
        let target : U32 := UScalar.ofNatCore compiler.function.code.val.length (by simpa using (show compiler.function.code.val.length < 2^32 by omega))
        exact WP.spec_mono (compiler_else_dead_raw ops law compiler state bt frame prior guard condition old target
          frames dead guardEq found rfl) (by simp)
  obtain ⟨⟨status, after⟩, call, _⟩ := WP.spec_imp_exists total
  rw [call, WP.spec_ok]
  intro accepted
  change status = .Ok () at accepted
  subst status
  obtain ⟨middle, observed⟩ := compiler_else_observation ops compiler after state bt call
  have result := compiler_observe_stack ops law middle state
  rw [observed, WP.spec_ok] at result
  exact result rfl
end Itasca.Runtime.Compiler

end

/-! ## CloseMapEffect -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Only the root frame emits an epilogue when its map is closed. -/
def closeMapEpilogue (reachable : Bool) (frame : runtime.compiler.Frame) : List runtime.bytecode.Instr :=
  match frame.kind with
  | .Body => [.Return frame.height (if scopeExitLive reachable frame then frame.results else 0#u32)]
  | _ => []

/-- Exact map mutation by an unguarded scope close. This retains the original
map entry and complete updated vector, rather than only the two exit fields. -/
theorem close_unguarded_map_effect {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame]) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val+state.pos.val ≤ Usize.max)
    (codeFits : compiler.function.code.val.length < Usize.max)
    (sourceFits : compiler.function.source_offsets.val.length < Usize.max)
    (emitCoordinateFits : compiler.function.body_start.val+compiler.next_source.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () → out.2.frames = rest ∧
        out.2.function.code.val = patchCode compiler.function.code.val frame.fixups.val target ++
          closeMapEpilogue compiler.reachable frame ∧
        ∃ original closed, compiler.function.controls.val[frame.map.val]? = some original ∧
          out.2.function.controls.val = compiler.function.controls.val.set frame.map.val closed ∧
          closed.start_pc = original.start_pc ∧ closed.source_start = original.source_start ∧
          closed.end_pc.val = target.val ∧
          closed.source_end.val = compiler.function.body_start.val+state.pos.val ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame,rest) := by
    simp only [alloc.vec.Vec.pop,frames,List.getLast?_concat,List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame,rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o,remaining,ho,hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  rw [compiler_pc_eq ops {compiler with frames := rest} target position]
  simp only [bind_ok,noIf]
  step with compiler_fixups ops {compiler with frames := rest} frame.fixups target 0#usize
    (by simp) branches as ⟨s,params,budget,batch,func,frames',reach,source,before,height,offsets,depths,
      result,after,hsnapshot,onlyCode,effect⟩
  simp only [compilerSnapshot,Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨code,rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map,back,hmap,hback⟩
  step as ⟨pcword,hpcword⟩
  step as ⟨coordinate,hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind,true)
      else if frame.end_reachable then .ok (frame.kind,true)
      else Aeneas.Std.bind (match frame.kind with
        | .Body | .Block | .Loop => (.ok false : Result Bool)
        | .Then => .ok true | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind,entered)))) = .ok (frame.kind,scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases live : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive,kind,live,ends,bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind,true)
      else if frame.end_reachable then .ok (frame.kind,true)
      else Aeneas.Std.bind (match frame.kind with
        | .Body | .Block | .Loop => (.ok false : Result Bool)
        | .Then => .ok true | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind,entered)))) _) _
  rw [choice,bind_ok]
  have mapLookup : compiler.function.controls.val[frame.map.val]? = some map := by
    simp [List.getElem?_eq_getElem mapFits,hmap]
  let closed := {map with source_end := coordinate,end_pc := pcword}
  let updated := {compiler with frames := rest,reachable := scopeExitLive compiler.reachable frame,function := {compiler.function with code,controls := back closed}}
  have mapEffect : updated.function.controls.val = compiler.function.controls.val.set frame.map.val closed := by
    simp [updated,hback,alloc.vec.Vec.set_val_eq]
  have exitPc : closed.end_pc.val = target.val := by
    dsimp only [closed]
    rw [hpcword]
    scalar_tac
  have exitSource : closed.source_end.val = compiler.function.body_start.val+state.pos.val := hcoordinate
  have codeLength : code.val.length = compiler.function.code.val.length := by
    simpa only [patch_code_length] using congrArg List.length effect
  cases kind : frame.kind
  case Body =>
    change WP.spec (Aeneas.Std.bind (.ok true) _) _
    rw [bind_ok]
    simp only [ite_true]
    change WP.spec (Aeneas.Std.bind (if scopeExitLive compiler.reachable frame then .ok frame.results else .ok 0#u32) _) _
    have choose : (if scopeExitLive compiler.reachable frame then .ok frame.results else .ok 0#u32) =
        (.ok (if scopeExitLive compiler.reachable frame then frame.results else 0#u32) : Result U32) := by split <;> rfl
    rw [choose,bind_ok]
    step with compiler_emit ops law updated _ (by simpa [updated,codeLength] using codeFits)
      (by simpa [updated] using sourceFits) (by simpa [updated] using emitCoordinateFits)
      as ⟨status,emitted,hEmitted⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok unit =>
      obtain ⟨budget,instructions,sources,rfl,emittedCode,_⟩ := hEmitted rfl
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_observe ops law _ state as ⟨out,hout,success⟩
      obtain ⟨_,_,_,_,_,_,hcode,_,_,_,_,hframes,hcontrols⟩ := hout success
      refine ⟨hframes,?_,map,closed,mapLookup,?_,rfl,rfl,exitPc,exitSource⟩
      · rw [hcode]
        simpa only [updated,effect,List.drop_zero,closeMapEpilogue,kind,ite_true] using emittedCode
      · rw [hcontrols]
        exact mapEffect
  all_goals
    change WP.spec (Aeneas.Std.bind (.ok false) _) _
    rw [bind_ok]
    simp only [Bool.false_eq_true,ite_false]
    step with compiler_observe ops law updated state as ⟨out,hout,success⟩
    obtain ⟨_,_,_,_,_,_,hcode,_,_,_,_,hframes,hcontrols⟩ := hout success
    refine ⟨hframes,?_,map,closed,mapLookup,?_,rfl,rfl,exitPc,exitSource⟩
    · rw [hcode]
      simpa [closeMapEpilogue,kind] using effect
    · rw [hcontrols]
      exact mapEffect

end Itasca.Runtime.Compiler

end
