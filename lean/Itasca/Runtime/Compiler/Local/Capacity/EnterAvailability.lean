import Itasca.Runtime.Compiler.Local.Capacity.ScopeDemand
import Itasca.Runtime.Compiler.Local.Capacity.ObserveBudgetAvailability
import Itasca.Runtime.Compiler.Local.Capacity.BudgetEffects
import Itasca.Runtime.Compiler.Local.Capacity.EmitAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterBlock

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
