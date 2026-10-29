import Itasca.Runtime.Compiler.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseBlock
import Itasca.Runtime.Compiler.Local.Capacity.ObserveBudgetAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseGuardedScope
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Capacity.CallbackCapacity

/-!
Availability of end callbacks for root bodies, ordinary scopes and guarded scopes. The dispatch proof retains each scope-specific allocation obligation.
-/

/-! ## Close Body Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Root closing accepts from retained branch-hole shapes and map ownership.
The implicit epilogue consumes one instruction, including for dead bodies. -/
theorem compiler_close_body_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (demand : CallbackDemand compiler state bound)
    (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (kind : frame.kind = .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Body .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, noIf]
  step with compiler_fixups ops { compiler with frames := rest } frame.fixups target 0#usize
    (by simp) branches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  simp only [kind,bind_ok,Bool.false_eq_true,ite_false]
  split <;> try simp only [bind_ok,Bool.false_eq_true,ite_false]
  all_goals try (split <;> simp only [bind_ok,Bool.false_eq_true,ite_false])
  all_goals
    change WP.spec (Aeneas.Std.bind (.ok true) _) _
    rw [bind_ok]
    simp only [ite_true,Bool.false_eq_true,ite_false,bind_ok]
    let closed (live : Bool) := {compiler with
      function := {compiler.function with
        code := code
        controls := back {map with source_end := coordinate,end_pc := pcword}}
      frames := rest
      reachable := live}
    have codeLength : code.length = compiler.function.code.length := by
      simp only [alloc.vec.Vec.length,effect,List.drop_zero,patch_code_length]
    have closedDemand (live : Bool) : CallbackDemand (closed live) state bound := by
      refine ⟨?_,?_,demand.sourceCapacity,?_,demand.sourceReserve,demand.coordinate,
        demand.instruction,demand.operands,demand.slots⟩
      · simpa only [closed,codeLength] using demand.pc
      · simpa only [closed,codeLength] using demand.codeCapacity
      · simpa only [closed,codeLength] using demand.codeReserve
    first
    | exact finish_op_available_effect ops bound available (closed true) state (closedDemand true)
        (.Return frame.height frame.results)
    | exact finish_op_available_effect ops bound available (closed false) state (closedDemand false)
        (.Return frame.height 0#u32)

end Itasca.Runtime.Compiler

end

/-! ## Guarded Scope Close Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_guarded_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (guard : Usize) (condition old : U32)
    (nonBody : frame.kind ≠ .Body) (hasIf : frame.if_pc = some guard)
    (guardCode : compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, hasIf]
  step with compiler_patch ops { compiler with frames := rest } guard (.zero condition) old target guardCode as
    ⟨status, patched, statusEq, patchedEffect⟩
  subst status
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have patchedBranches := patchedEffect.branch_sites (List.getElem?_eq_some_iff.mp guardCode).1 branches
  obtain ⟨patchedCode, rfl, codeSet⟩ := patchedEffect
  step with compiler_fixups_after_if ops _ frame.fixups target 0#usize
    (by simp) patchedBranches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) = .ok (frame.kind, scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases reach : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive, kind, reach, ends, bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) _) _
  rw [choice, bind_ok]
  have notBody : (match frame.kind with
      | .Body => (.ok true : Result Bool)
      | .Block | .Loop | .Then | .Else => .ok false) = .ok false := by
    cases kind : frame.kind <;> simp_all
  change WP.spec (Aeneas.Std.bind (match frame.kind with
    | .Body => (.ok true : Result Bool)
    | .Block | .Loop | .Then | .Else => .ok false) _) _
  rw [notBody, bind_ok]
  simp only [Bool.false_eq_true, ite_false]
  let closed := {compiler with
    function := {compiler.function with
      code := code
      controls := back {map with source_end := coordinate,end_pc := pcword}}
    frames := rest
    reachable := scopeExitLive compiler.reachable frame}
  exact compiler_observe_available_budget ops bound available closed state request slotsFit

end Itasca.Runtime.Compiler

end

/-! ## Scope Close Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Non-root scope closing accepts from retained holes, map ownership, and
independent observer demand, preserving every compiler resource counter. -/
theorem compiler_close_scope_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A)
    (state : Itasca.code.OpIterState) (frame : runtime.compiler.Frame)
    (rest : alloc.vec.Vec runtime.compiler.Frame) (target : U32)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (nonBody : frame.kind ≠ .Body) (noIf : frame.if_pc = none)
    (position : target.val = compiler.function.code.val.length)
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max)
    (request : state.vals.length ≤ bound)
    (slotsFit : compiler.function.local_slots.val + 2*state.vals.length ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ out.2.budget = compiler.budget ⦄ := by
  have pop : alloc.vec.Vec.pop Global compiler.frames = .ok (some frame, rest) := by
    simp only [alloc.vec.Vec.pop, frames, List.getLast?_concat, List.dropLast_concat]
    congr 2
    apply alloc.vec.Vec.ext
    simp
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end
  have popSpec : alloc.vec.Vec.pop Global compiler.frames ⦃ out => out = (some frame, rest) ⦄ := by
    rw [pop]
    simp [WP.spec_ok]
  step with popSpec as ⟨o, remaining, ho, hremaining⟩
  subst o remaining
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [compiler_pc_eq ops { compiler with frames := rest } target position]
  simp only [bind_ok, noIf]
  step with compiler_fixups ops { compiler with frames := rest } frame.fixups target 0#usize
    (by simp) branches as ⟨s, params, budget, batch, func, frames', reach, source, before,
      height, offsets, depths, result, after, hsnapshot, onlyCode, effect⟩
  simp only [compilerSnapshot, Prod.mk.injEq] at hsnapshot
  rcases hsnapshot with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨code, rfl⟩ := onlyCode
  simp only [bind_ok]
  step as ⟨map, back, hmap, hback⟩
  step as ⟨pcword, hpcword⟩
  step as ⟨coordinate, hcoordinate⟩
  have choice : (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) = .ok (frame.kind, scopeExitLive compiler.reachable frame) := by
    cases kind : frame.kind <;> cases reach : compiler.reachable <;> cases ends : frame.end_reachable <;>
      simp [scopeExitLive, kind, reach, ends, bind_ok]
  change WP.spec (Aeneas.Std.bind (if compiler.reachable then .ok (frame.kind, true)
      else if frame.end_reachable then .ok (frame.kind, true)
      else Aeneas.Std.bind (match frame.kind with
          | .Body | .Block | .Loop => (.ok false : Result Bool)
          | .Then => .ok true
          | .Else => .ok false) (fun thenLabel =>
        Aeneas.Std.bind (if thenLabel then .ok frame.entry_reachable else .ok false)
          (fun entered => .ok (frame.kind, entered)))) _) _
  rw [choice, bind_ok]
  have notBody : (match frame.kind with
      | .Body => (.ok true : Result Bool)
      | .Block | .Loop | .Then | .Else => .ok false) = .ok false := by
    cases kind : frame.kind <;> simp_all
  change WP.spec (Aeneas.Std.bind (match frame.kind with
    | .Body => (.ok true : Result Bool)
    | .Block | .Loop | .Then | .Else => .ok false) _) _
  rw [notBody, bind_ok]
  simp only [Bool.false_eq_true, ite_false]
  let closed := {compiler with
    function := {compiler.function with
      code := code
      controls := back {map with source_end := coordinate,end_pc := pcword}}
    frames := rest
    reachable := scopeExitLive compiler.reachable frame}
  exact compiler_observe_available_budget ops bound available closed state request slotsFit

end Itasca.Runtime.Compiler

end

/-! ## End Dispatch Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every end callback accepts from retained scope ownership and independent
capacity, including the nonvoid dead-body epilogue. Target PCs are constructed
from numeric bounds; source guard/fixup shapes discharge actual patching. -/
theorem compiler_end_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (capacity : CallbackCapacity compiler state bound 1)
    (frame : runtime.compiler.Frame) (rest : alloc.vec.Vec runtime.compiler.Frame)
    (frames : compiler.frames.val = rest.val ++ [frame])
    (rootNoGuard : frame.kind = .Body → frame.if_pc = none)
    (guardOwned : ∀ guard, frame.if_pc = some guard → ∃ condition old,
      compiler.function.code.val[guard.val]? = some (.JumpIfZero condition old))
    (branches : BranchSites compiler.function.code.val frame.fixups.val)
    (mapFits : frame.map.val < compiler.function.controls.val.length)
    (coordinateFits : compiler.function.body_start.val + state.pos.val ≤ Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_end ops compiler state .Block .Empty ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  have fits : compiler.function.code.length < 2^UScalarTy.U32.numBits := by
    have room := capacity.pc
    scalar_tac
  let target := U32.ofNatCore compiler.function.code.length fits
  have position : target.val = compiler.function.code.val.length := U32.ofNatCore_val_eq fits
  by_cases root : frame.kind = .Body
  · exact compiler_close_body_available ops bound available compiler state (capacity.one (by decide))
      frame rest target frames root (rootNoGuard root) position branches mapFits coordinateFits
  · cases guardPc : frame.if_pc with
    | none =>
      apply WP.spec_mono (compiler_close_scope_available ops bound available compiler state frame rest target frames root
        guardPc position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩
    | some guard =>
      obtain ⟨condition,old,guardCode⟩ := guardOwned guard guardPc
      apply WP.spec_mono (compiler_close_guarded_scope_available ops bound available compiler state frame rest target frames
        guard condition old root guardPc guardCode position branches mapFits coordinateFits capacity.operands capacity.slots)
      intro out post
      rw [post.2]
      exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end
