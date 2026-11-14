import Itasca.Runtime.Compiler.Local.Callbacks.Control.EndContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ElseContracts
import Itasca.Runtime.Compiler.Local.Callbacks.Effects.OrdinaryEffects
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CompilerCodeMonotoneCallbacks
import Itasca.Runtime.Compiler.Local.Callbacks.Calls.CallbackBounds
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Control.ScopeFrameStart
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerTableScratchLiteral
import Itasca.Runtime.Compiler.Local.Capacity.ControlCapacity
import Itasca.Runtime.Compiler.Local.Relations.Table.ControlTablePreservation
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Relations.Control.ControlObservedLayout
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
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ branch old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction branch old) := by
    intro queried selected
    have same : queried = guard := Option.some.inj (selected.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, old, guardCode⟩
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total ops law compiler state bt frame prior frames guardSites
    (by intro live; exact ⟨fixupsFit, codeFits, offsetsFit, coordinateFits⟩)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops compiler after state bt (.Ok ()) called
  exact effect.live_success law ⟨frame, prior, guard, condition, old, target, frames, reachable, guardPc, guardCode, position⟩

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
  have guardSites : ∀ queried, frame.if_pc = some queried →
      ∃ branch old, compiler.function.code.val[queried.val]? = some (BranchKind.instruction branch old) := by
    intro queried selected
    have same : queried = guard := Option.some.inj (selected.symm.trans guardPc)
    subst queried
    exact ⟨.zero condition, old, guardCode⟩
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total ops law compiler state bt frame prior frames guardSites
    (by intro live; simp only [reachable, Bool.false_eq_true] at live)
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.inv ops compiler after state bt (.Ok ()) called
  obtain ⟨reach, published, restore, finished⟩ := effect.dead_success law frame prior frames reachable
  rw [guardPc] at finished
  have code := finished.guard_success condition old target guardCode position
  exact ⟨reach, code, published⟩

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
  apply runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_else.total ops law compiler state bt frame prior frames
  · intro guard selected
    rw [noGuard] at selected
    cases selected
  · intro reachable
    exact ⟨fixupsFit, codeFits, offsetsFit, coordinateFits⟩

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
  have normal := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.total ops law compiler state .Block .Empty
    ⟨frame, rest, frames, branches, (by intro queried selected; rw [noIf] at selected; cases selected),
      mapFits, coordinateFits, (by intro body; exact ⟨codeFits, sourceFits, emitCoordinateFits⟩)⟩
  obtain ⟨⟨status, after⟩, called, _⟩ := WP.spec_imp_exists normal
  rw [called, WP.spec_ok]
  intro successful
  dsimp only at successful ⊢
  subst status
  have effect := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end.inv ops compiler after state .Block .Empty (.Ok ()) called
  obtain ⟨remaining, reachable, code, original, closed, selected, controls, start, sourceStart, endPc, sourceEnd⟩ :=
    effect.unguarded_success law frame rest target frames position noIf branches mapFits
  refine ⟨remaining, ?_, original, closed, selected, controls, start, sourceStart, endPc, sourceEnd⟩
  cases label : frame.kind <;> simpa only [closeMapEpilogue, endReachable, scopeExitLive, label] using code

end Itasca.Runtime.Compiler

end
