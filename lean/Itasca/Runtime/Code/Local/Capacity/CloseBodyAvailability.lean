import Itasca.Runtime.Code.Local.Capacity.FinishBudgetAvailability
import Itasca.Runtime.Code.Local.Callbacks.Control.CloseBlock

namespace Itasca.Runtime.Code
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
      simp only [alloc.vec.Vec.length,effect,List.drop_zero,patchCode_length]
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

end Itasca.Runtime.Code
