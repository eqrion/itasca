import Itasca.Runtime.Compiler.Local.Capacity.UnreachableAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CompilerCodeMonotoneControl
import Itasca.Runtime.Compiler.Local.Callbacks.Control.CloseScope
import Itasca.Runtime.Compiler.Local.Lowering.Local.LoweringLocal

/-!
Sections, each formerly its own module: EndDispatchAvailability, EnterAvailability, ScopeAvailability, ReturnAvailability.
-/

/-! ## EndDispatchAvailability -/

section

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

end

/-! ## EnterAvailability -/

section

/-!
Allocation availability for scope publication and entry without emitted code. The publication reserve is discharged before constructing the entered compiler state.
-/

/-! ## Scope Publication Available -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Exact publication suffix of the extracted scope-opening callback. Its
connection to scope entry is checked by definitional equality in the entry
acceptance proofs. This helper adds no external execution model. -/
noncomputable def scopePublication {A : Type} (ops : runtime.platform.Alloc A)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (kind : Itasca.code.LabelKind) (signature : runtime.compiler.Signature)
    (height : U32) (sourceStart valueHeight : Usize) (startPc : U32) (ifPc : Option Usize) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.FunctionCompiler A) := do
  let map := alloc.vec.Vec.len compiler.function.controls
  let (r4, b) ←
    runtime.compiler.Budget.charge ops
      compiler.budget runtime.compiler.CompileResource.Controls
  let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
  match cf4 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let i1 ← lift (UScalar.cast .Usize startPc)
    let (r5, b1, v) ←
      runtime.compiler.Budget.push ops b
        compiler.function.controls
        ({
           kind,
           source_start := sourceStart,
           source_end := 0#usize,
           start_pc := i1,
           end_pc := 0#usize,
           stack_height := valueHeight,
           parameters := signature.params,
           results := signature.results
         } : _root_.Itasca.runtime.compiler.ControlMap)
    let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf5 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r6, b2, v1) ←
        runtime.compiler.Budget.push ops b1
          compiler.frames
          ({
             map,
             kind,
             height,
             params := signature.param_slots,
             results := signature.result_slots,
             start_pc := startPc,
             if_pc := ifPc,
             entry_reachable := compiler.reachable,
             end_reachable := false,
             fixups := (alloc.vec.Vec.new Std.Usize)
           } : _root_.Itasca.runtime.compiler.Frame)
      let cf6 ←
        core.result.Result.Insts.CoreOpsTry.branch r6
      match cf6 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        runtime.compiler.FunctionCompiler.observe
          ops
          {
            compiler
              with
              budget := b2,
              function :=
                { compiler.function with controls := v },
              frames := v1
          } state
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r7 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame
            _root_.Itasca.error.VisitError) residual
        Result.ok (r7,
          {
            compiler
              with
              budget := b2,
              function :=
                { compiler.function with controls := v },
              frames := v1
          })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r6 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame
          _root_.Itasca.error.VisitError) residual
      Result.ok (r6,
        {
          compiler
            with
            budget := b1,
            function := { compiler.function with controls := v }
        })
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r5 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame
        _root_.Itasca.error.VisitError) residual
    Result.ok (r5, { compiler with budget := b })

/-- Publishing a bounded scope succeeds and changes precisely its control
counter. Instruction and branch/local budgets are retained. -/
theorem scope_publication_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : ScopeDemand compiler state bound) (kind : Itasca.code.LabelKind)
    (signature : runtime.compiler.Signature) (height : U32)
    (sourceStart valueHeight : Usize) (startPc : U32) (ifPc : Option Usize) :
    scopePublication ops compiler state kind signature height sourceStart valueHeight startPc ifPc ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .controls then 1 else 0) ⦄ := by
  unfold scopePublication
  step with charge_counter_available ops .controls compiler.budget demand.control
    as ⟨status,budget,accepted,used,same,usedEq⟩
  rw [accepted,same]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step as ⟨start,hstart⟩
  step with budget_push_available ops bound available (ChargeCounter.controls.replace compiler.budget used)
    compiler.function.controls
    ⟨kind,sourceStart,0#usize,start,0#usize,valueHeight,signature.params,signature.results⟩
    demand.mapsCapacity demand.mapsReserve as ⟨status,budget,maps,accepted,same,_⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available (ChargeCounter.controls.replace compiler.budget used)
    compiler.frames
    ⟨alloc.vec.Vec.len compiler.function.controls,kind,height,signature.param_slots,
      signature.result_slots,startPc,ifPc,compiler.reachable,false,alloc.vec.Vec.new Usize⟩
    demand.framesCapacity demand.framesReserve as ⟨status,budget,frames,accepted,same,_⟩
  subst status budget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  let framed := {compiler with
    budget := ChargeCounter.controls.replace compiler.budget used
    function := {compiler.function with controls := maps}
    frames := frames}
  apply WP.spec_mono (compiler_observe_available_budget ops bound available framed state demand.operands demand.slots)
  intro out post
  rw [post.2]
  exact ⟨post.1,.of_counter .controls compiler.budget used 1
    (by simp [ChargeCounter.used] at usedEq ⊢; omega)
    (by simp [ChargeCounter.used] at usedEq ⊢; omega)⟩

end Itasca.Runtime.Compiler

end

/-! ## Enter Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Opening an ordinary block or a dead scope accepts without emitting code.
Its budget effect is exactly one control, with all other counters retained. -/
theorem compiler_enter_without_emission_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : ScopeDemand compiler state bound) (ctrl : Itasca.code.Ctrl)
    (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (noThen : compiler.reachable = true → kind ≠ .Then)
    (noLoop : compiler.reachable = true → kind ≠ .Loop) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .controls then 1 else 0) ⦄ := by
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp [alloc.vec.Vec.len,controls] at lengthEq
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last,hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len,controls] at hlast; omega
  step as ⟨actual,hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast,controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig,hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots
    (by simpa [alloc.vec.Vec.deref] using valuesFit)
    (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height,hheight⟩
  have coordinate := demand.coordinate
  step as ⟨source,hsource⟩
  cases kind
  all_goals
    simp only [bind_ok,Bool.and_eq_true,← ite_and,Bool.false_eq_true,and_false,and_true,
      ite_false,if_false]
    try rw [if_neg (show ¬ compiler.reachable = true from fun active => noThen active rfl)]
    step with compiler_pc_available ops compiler demand.pc as ⟨status,first,same,pc,accepted,_⟩
    subst first
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Bool.and_eq_true,← ite_and,
      Bool.false_eq_true,and_false,and_true,ite_false,if_false]
    try rw [if_neg (show ¬ compiler.reachable = true from fun active => noLoop active rfl)]
    change scopePublication ops compiler state _ signature height source ctrl.value_stack_base pc none ⦃ out => _ ⦄
    exact scope_publication_available ops bound available compiler state demand _ signature height source
      ctrl.value_stack_base pc none

end Itasca.Runtime.Compiler

end

end

/-! ## ScopeAvailability -/

section

/-!
Availability of block, loop and if entry callbacks under source stack bounds. The common theorem retains the branch-specific allocation premises.
-/

/-! ## Enter If Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Live if opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_if_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (front : List valtype) (layout : CompilerLayout compiler (front ++ [.I32]))
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Then bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp [alloc.vec.Vec.len,controls] at lengthEq
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last,hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len,controls] at hlast; omega
  step as ⟨actual,hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast,controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig,hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots
    (by simpa [alloc.vec.Vec.deref] using valuesFit)
    (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height,hheight⟩
  have coordinate := scope.coordinate
  step as ⟨source,hsource⟩
  simp only [bind_ok,
    live,Bool.false_eq_true,ite_false,ite_true]
  obtain ⟨condition,read,_⟩ := last_operand ops compiler front .I32 layout
  rw [read]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_emit_available_frame ops bound available compiler (.JumpIfZero condition core.num.U32.MAX)
    demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
    demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,codeAppend,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have emittedPc : emitted.function.code.length ≤ U32.max := by
    rw [frame]
    simpa [alloc.vec.Vec.length,codeAppend] using pcRoom
  step with compiler_pc_available ops emitted emittedPc as ⟨status,first,same,pc,accepted,_⟩
  subst first
  rw [accepted]
  have emittedLive : emitted.reachable = true := by rw [frame]; exact live
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,Bool.false_eq_true,ite_false,ite_self]
  change scopePublication ops emitted state .Then signature height source ctrl.value_stack_base pc
    (some (alloc.vec.Vec.len compiler.function.code)) ⦃ out => _ ⦄
  have emittedScope : ScopeDemand emitted state bound := by
    rw [frame]
    refine ⟨?_,scope.coordinate,scope.mapsCapacity,scope.mapsReserve,scope.framesCapacity,
      scope.framesReserve,scope.control,scope.operands,scope.slots⟩
    simpa [alloc.vec.Vec.length,codeAppend] using pcRoom
  have budgetEq : emitted.budget = {compiler.budget with instructions := used} := by rw [frame]
  have firstEffect : CompilationBudgetEffect compiler.budget emitted.budget
      (fun counter => if counter = .instructions then 1 else 0) := by
    rw [budgetEq]
    exact .of_counter .instructions compiler.budget used 1
      (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
  apply WP.spec_mono (scope_publication_available ops bound available emitted state emittedScope .Then
    signature height source ctrl.value_stack_base pc (some (alloc.vec.Vec.len compiler.function.code)))
  intro out post
  exact ⟨post.1,(firstEffect.trans post.2).weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Compiler

end

/-! ## Enter Loop Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Live loop opening accepts with one instruction and one control charge.
All control-map and frame storage is independently bounded. -/
theorem compiler_enter_loop_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (live : compiler.reachable = true) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state .Loop bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have nonempty : alloc.vec.Vec.len state.ctrls ≠ 0#usize := by
    intro same
    have lengthEq := congrArg UScalar.val same
    simp [alloc.vec.Vec.len,controls] at lengthEq
  unfold runtime.compiler.control.FunctionCompiler.enter
  rw [if_neg nonempty]
  step as ⟨last,hlast⟩
  have atLast : last.val = prior.length := by simp [alloc.vec.Vec.len,controls] at hlast; omega
  step as ⟨actual,hactual⟩
  have actualEq : actual = ctrl := by simpa [atLast,controls] using hactual
  rw [actualEq]
  step with block_signature compiler.signatures bt signature selected as ⟨sig,hsig⟩
  subst sig
  step with control_stack_height state.vals.deref ctrl.value_stack_base compiler.function.local_slots
    (by simpa [alloc.vec.Vec.deref] using valuesFit)
    (by simpa [alloc.vec.Vec.deref] using heightFits) as ⟨height,hheight⟩
  have coordinate := scope.coordinate
  step as ⟨source,hsource⟩
  simp only [bind_ok,
    live,Bool.false_eq_true,ite_false,ite_true]
  step with compiler_pc_available ops compiler demand.pc as ⟨status,first,same,pc,accepted,_⟩
  subst first
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,live,ite_true]
  step with compiler_emit_available_frame ops bound available compiler .LoopHead demand.pc demand.codeCapacity
    demand.sourceCapacity demand.codeReserve demand.sourceReserve demand.coordinate demand.instruction
    as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,codeAppend,_⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  change scopePublication ops emitted state .Loop signature height source ctrl.value_stack_base pc none ⦃ out => _ ⦄
  have emittedScope : ScopeDemand emitted state bound := by
    rw [frame]
    refine ⟨?_,scope.coordinate,scope.mapsCapacity,scope.mapsReserve,scope.framesCapacity,
      scope.framesReserve,scope.control,scope.operands,scope.slots⟩
    simpa [alloc.vec.Vec.length,codeAppend] using pcRoom
  have budgetEq : emitted.budget = {compiler.budget with instructions := used} := by rw [frame]
  have firstEffect : CompilationBudgetEffect compiler.budget emitted.budget
      (fun counter => if counter = .instructions then 1 else 0) := by
    rw [budgetEq]
    exact .of_counter .instructions compiler.budget used 1
      (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)
  apply WP.spec_mono (scope_publication_available ops bound available emitted state emittedScope .Loop
    signature height source ctrl.value_stack_base pc none)
  intro out post
  exact ⟨post.1,(firstEffect.trans post.2).weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Compiler

end

/-! ## Scope Availability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Every raw observed stack entry occupies at most two compiler words. -/
theorem stack_words_le_twice_length (values : List Itasca.code.StackType) :
    stackWords values ≤ 2*values.length := by
  induction values with
  | nil => simp [stackWords]
  | cons value rest ih =>
    have widthBound : compilerStackWidth value ≤ 2 := by
      cases value with
      | Bot => decide
      | Val ty => cases ty <;> decide
    simp only [stackWords,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
    omega

/-- All scope kinds accept under source control/signature information and
independent demands. Live if entry alone needs a condition layout; dead code
requires no live operand layout. Scope height arithmetic follows from the
same conservative slot bound used by ordinary callbacks. -/
theorem compiler_enter_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (scope : ScopeDemand compiler state bound)
    (ctrl : Itasca.code.Ctrl) (prior : List Itasca.code.Ctrl) (kind : Itasca.code.LabelKind)
    (bt : Itasca.signature.BlockType) (signature : runtime.compiler.Signature)
    (controls : state.ctrls.val = prior ++ [ctrl])
    (selected : SignatureAt compiler.signatures bt signature)
    (valuesFit : ctrl.value_stack_base.val ≤ state.vals.val.length)
    (pcRoom : compiler.function.code.length + 1 ≤ U32.max)
    (conditionLayout : compiler.reachable = true → kind = .Then →
      ∃ front, CompilerLayout compiler (front ++ [.I32])) :
    runtime.compiler.control.FunctionCompiler.enter ops compiler state kind bt ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions ∨ counter = .controls then 1 else 0) ⦄ := by
  have heightFits : compiler.function.local_slots.val +
      stackWords (state.vals.val.take ctrl.value_stack_base.val) ≤ U32.max := by
    have words := stack_words_le_twice_length (state.vals.val.take ctrl.value_stack_base.val)
    have lengthBound : (state.vals.val.take ctrl.value_stack_base.val).length ≤ state.vals.val.length := by
      simp only [List.length_take]; exact Nat.min_le_right _ _
    have room := scope.slots
    simp only [alloc.vec.Vec.length] at room
    omega
  by_cases loopEntry : compiler.reachable = true ∧ kind = .Loop
  · obtain ⟨live,rfl⟩ := loopEntry
    exact compiler_enter_loop_available ops bound available compiler state demand scope ctrl prior bt signature
      controls selected valuesFit heightFits pcRoom live
  · by_cases ifEntry : compiler.reachable = true ∧ kind = .Then
    · obtain ⟨live,rfl⟩ := ifEntry
      obtain ⟨front,layout⟩ := conditionLayout live rfl
      exact compiler_enter_if_available ops bound available compiler state demand scope ctrl prior bt signature
        controls selected valuesFit heightFits pcRoom front layout live
    · apply WP.spec_mono (compiler_enter_without_emission_available ops bound available compiler state scope ctrl prior
        kind bt signature controls selected valuesFit heightFits
        (by intro live same; exact ifEntry ⟨live,same⟩)
        (by intro live same; exact loopEntry ⟨live,same⟩))
      intro out post
      exact ⟨post.1,post.2.weaken (by intro counter; cases counter <;> simp)⟩

end Itasca.Runtime.Compiler

end

end

/-! ## ReturnAvailability -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
set_option maxRecDepth 4096

/-- Return accepts from a retained root frame and a source-justified result
width. Dead returns need neither a live root lookup nor result operands. -/
theorem compiler_return_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (state : Itasca.code.OpIterState)
    (demand : CallbackDemand compiler state bound) (body : runtime.compiler.Frame)
    (bodyFrame : compiler.reachable = true → compiler.frames.val[0]? = some body)
    (height : compiler.reachable = true → body.results.val ≤ compiler.height.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return ops compiler state ⦃ out =>
      out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget out.2.budget
        (fun counter => if counter = .instructions then 1 else 0) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_return
  by_cases live : compiler.reachable = true
  · rw [if_pos live]
    have framesBound : 0 < compiler.frames.length := (List.getElem?_eq_some_iff.mp (bodyFrame live)).1
    step as ⟨frame,hframe⟩
    have same : frame = body := hframe.trans (List.getElem?_eq_some_iff.mp (bodyFrame live)).2
    rw [same]
    have resultFits := height live
    step as ⟨value,hvalue⟩
    cases value with
    | none => simp only at hvalue; omega
    | some source =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      step with compiler_emit_available_frame ops bound available compiler (.Return source body.results)
        demand.pc demand.codeCapacity demand.sourceCapacity demand.codeReserve demand.sourceReserve
        demand.coordinate demand.instruction
        as ⟨status,emitted,accepted,used,code,sources,frame,usedEq,_,_⟩
      rw [accepted]
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
      have slotsFit : emitted.function.local_slots.val + 2*state.vals.length ≤ U32.max := by
        rw [frame]; exact demand.slots
      apply WP.spec_mono (compiler_observe_available_budget ops bound available {emitted with reachable := false}
        state demand.operands slotsFit)
      intro out post
      rw [post.2]
      have budgetEq : emitted.budget = {compiler.budget with instructions := used} := by rw [frame]
      change out.1 = .Ok () ∧ CompilationBudgetEffect compiler.budget emitted.budget _
      rw [budgetEq]
      exact ⟨post.1,.of_counter .instructions compiler.budget used 1
        (by simp [ChargeCounter.used]; omega) (by simp [ChargeCounter.used]; omega)⟩
  · rw [if_neg live]
    apply WP.spec_mono (compiler_observe_available_budget ops bound available compiler
      state demand.operands demand.slots)
    intro out post
    rw [post.2]
    exact ⟨post.1,(CompilationBudgetEffect.refl compiler.budget).weaken (by intro counter; omega)⟩

end Itasca.Runtime.Compiler

end
