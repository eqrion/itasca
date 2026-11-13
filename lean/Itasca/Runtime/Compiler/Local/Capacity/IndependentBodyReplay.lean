import Itasca.Runtime.Compiler.Local.Relations.Instructions.WellFormed
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Lowering.Simd.SimdMemoryValid
import Itasca.Visitor.BodyReplay
import Itasca.Runtime.Compiler.Local.Demand.IndependentBodyDemand

/-!
Sections, each formerly its own module: OperandBounds, SimdCapacity, IndependentBodyReplay.
-/

/-! ## OperandBounds -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

@[step] theorem slots_fit_spec (f : runtime.bytecode.CompiledFunction) (start count : U32) :
    runtime.bytecode.CompiledFunction.slots_fit f start count
      ⦃ out => out = true ↔ start.val + count.val ≤ f.slot_count.val ⦄ := by
  unfold runtime.bytecode.CompiledFunction.slots_fit
  split
  · step as ⟨remaining, hremaining⟩
    simp only [decide_eq_true_eq]
    scalar_tac
  · simp only [WP.spec_ok, Bool.false_eq_true, false_iff]
    scalar_tac

theorem slots_fit_true (f : runtime.bytecode.CompiledFunction) (start count : U32)
    (checked : runtime.bytecode.CompiledFunction.slots_fit f start count = .ok true) :
    start.val + count.val ≤ f.slot_count.val := by
  have correct := slots_fit_spec f start count
  rw [checked] at correct
  simp only [WP.spec_ok, true_iff] at correct
  exact correct

private theorem checked_and (first second : Result Bool)
    (checked : (do let b ← first; if b then second else .ok false) = .ok true) :
    first = .ok true ∧ second = .ok true := by
  obtain ⟨value, firstRun, checked⟩ := bind_ok_inv _ _ _ checked
  cases value with
  | false => simp at checked
  | true => exact ⟨firstRun, checked⟩

theorem copy_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Copy dst src) = .ok true) :
    dst.val + 1 ≤ f.slot_count.val ∧ src.val + 1 ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨left, right⟩ := checked_and _ _ checked
  have dl := slots_fit_true f dst 1#u32 left
  have sl := slots_fit_true f src 1#u32 right
  scalar_tac

theorem copy2_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst src : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Copy2 dst src) = .ok true) :
    dst.val + 2 ≤ f.slot_count.val ∧ src.val + 2 ≤ f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨left, right⟩ := checked_and _ _ checked
  have dl := slots_fit_true f dst 2#u32 left
  have sl := slots_fit_true f src 2#u32 right
  scalar_tac

theorem const32_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst : U32) (value : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Const32 dst value) = .ok true) :
    dst.val < f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  have bound := slots_fit_true f dst 1#u32 checked
  scalar_tac

theorem const64_valid_bounds (f : runtime.bytecode.CompiledFunction) (dst : U32) (value : U64)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.Const64 dst value) = .ok true) :
    dst.val < f.slot_count.val := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  have bound := slots_fit_true f dst 1#u32 checked
  scalar_tac

theorem jump_if_zero_valid_bounds (f : runtime.bytecode.CompiledFunction) (cond target : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.JumpIfZero cond target) = .ok true) :
    cond.val < f.slot_count.val ∧ target.val < f.code.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨slot, targetRun⟩ := checked_and _ _ checked
  have bound := slots_fit_true f cond 1#u32 slot
  simp only [lift, bind_ok] at targetRun
  have targetBound := Result.ok_injective targetRun
  scalar_tac

theorem jump_if_non_zero_valid_bounds (f : runtime.bytecode.CompiledFunction) (cond target : U32)
    (checked : runtime.bytecode.CompiledFunction.instruction_valid f (.JumpIfNonZero cond target) = .ok true) :
    cond.val < f.slot_count.val ∧ target.val < f.code.length := by
  simp only [runtime.bytecode.CompiledFunction.instruction_valid,runtime.bytecode.CompiledFunction.other_valid,
    runtime.bytecode.Instr.scalar, runtime.bytecode.Instr.load,
    runtime.bytecode.Instr.store, runtime.bytecode.Instr.simd, bind_ok] at checked
  obtain ⟨slot, targetRun⟩ := checked_and _ _ checked
  have bound := slots_fit_true f cond 1#u32 slot
  simp only [lift, bind_ok] at targetRun
  have targetBound := Result.ok_injective targetRun
  scalar_tac

end Itasca.Runtime.Compiler

end

/-! ## SimdCapacity -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

theorem simd_view_disjoint (instruction : runtime.bytecode.Instr) (op dst a entry : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry))) :
    runtime.bytecode.Instr.scalar instruction = .ok none ∧
    runtime.bytecode.Instr.load instruction = .ok none ∧
    runtime.bytecode.Instr.store instruction = .ok none := by
  cases instruction
  all_goals simp only [runtime.bytecode.Instr.simd,Result.ok.injEq,Option.some.injEq,reduceCtorEq,Prod.mk.injEq] at view
  all_goals first | contradiction | exact ⟨rfl,rfl,rfl⟩

theorem simd_valid_bounds (compiled : runtime.bytecode.CompiledFunction)
    (instruction : runtime.bytecode.Instr) (op dst a entry wa wb wc wr : U32)
    (view : runtime.bytecode.Instr.simd instruction = .ok (some (op,dst,a,entry)))
    (shape : runtime.bytecode.simd_shape op = .ok (some (wa,wb,wc,wr)))
    (checked : runtime.bytecode.CompiledFunction.instruction_valid compiled instruction = .ok true) :
    a.val + wa.val + wb.val + wc.val ≤ compiled.slot_count.val ∧
    dst.val + wr.val ≤ compiled.slot_count.val ∧ entry.val < compiled.simd.length := by
  obtain ⟨scalar,load,store⟩ := simd_view_disjoint instruction op dst a entry view
  unfold runtime.bytecode.CompiledFunction.instruction_valid at checked
  simp only [scalar,load,store,view,shape,bind_ok,uncurry_apply_pair] at checked
  obtain ⟨xy,xyRun,checked⟩ := bind_ok_inv _ _ _ checked
  obtain ⟨xyz,xyzRun,checked⟩ := bind_ok_inv _ _ _ checked
  have xyFact := UScalar.add_equiv wa wb
  rw [xyRun] at xyFact
  have xyVal : xy.val = wa.val+wb.val := xyFact.2.1
  have xyzFact := UScalar.add_equiv xy wc
  rw [xyzRun] at xyzFact
  have xyzVal : xyz.val = xy.val+wc.val := xyzFact.2.1
  obtain ⟨fits,fitRun,checked⟩ := bind_ok_inv _ _ _ checked
  cases fits with
  | false => simp at checked
  | true =>
    simp only [ite_true] at checked
    obtain ⟨fits,fitOut,checked⟩ := bind_ok_inv _ _ _ checked
    cases fits with
    | false => simp at checked
    | true =>
      have inputs := slots_fit_true compiled a xyz fitRun
      have outputs := slots_fit_true compiled dst wr fitOut
      simp only [ite_true,lift,bind_ok,Result.ok.injEq,decide_eq_true_eq] at checked
      exact ⟨by omega,outputs,by simpa using checked⟩
end Itasca.Runtime.Compiler

end

/-! ## IndependentBodyReplay -/

section

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca Itasca.VisitorTrace

/-- Independent body validity constructs its reference run internally, then
replays only its reached steps. The remaining compiler-specific obligation is
the local resource/prefix refinement; an accepted callback trace or successful
target body is not an input to this theorem. -/
theorem independent_body_accepted_replay {W : Type} (target : code.OpVisitor W)
     (data : Slice U8) (env : metadata.Env) (ctx : code.Context)
    (index : U32) (limits : Profile.EnvironmentWithinLimits env)
    (size : data.length ≤ Itasca.limits.MAX_FUNCTION_BYTES.val)
    (body : Wasm2.Validated data env ctx.locals index)
    (related : code.BodyState → List Observation → W → Prop) (before : W)
    (initial : ∀ st, code.initial_state env index = .ok (.Ok st) →
      related st [] before)
    (steps : ReachedBody.AcceptingSuffixRefinement recorder target data env ctx index (independentBodyLog data env ctx index) related) :
    code.validate_body_with target data env ctx index before ⦃ result => result.1 = .Ok () ∧
      ∃ closed, related closed (independentBodyLog data env ctx index) result.2 ∧
        closed.core.ctrls.val = [] ∧ closed.core.pos = Slice.len data ⦄ := by
  have reference := independentBodyLog.of_valid data env ctx index limits size body
  exact code.validate_body_with.accepted_suffix_replay_on recorder target data env ctx index
    related (independentBodyLog data env ctx index)
    steps [] before initial reference

end Itasca.Runtime.Compiler

end
