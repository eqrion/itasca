import Itasca.Runtime.Compiler.Local.Capacity.BudgetAvailability
import Itasca.Runtime.Compiler.Local.Callbacks.Observation.Observe

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- Observation of one scalar, reference, SIMD, or polymorphic-bottom value
accepts when its independently computed slot width and reserve request fit. -/
theorem observe_value_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (before : alloc.vec.Vec U32)
    (height : U32) (ty : Itasca.code.StackType)
    (fits : before.length < Usize.max) (request : before.length + 1 ≤ bound)
    (slotsFit : height.val + compilerStackWidth ty ≤ U32.max) :
    runtime.compiler.observe_value ops budget before height ty ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧ out.2.2.1.val = before.val ++ [height] ∧
      out.2.2.2.val = height.val + compilerStackWidth ty ⦄ := by
  unfold runtime.compiler.observe_value
  step with budget_push_available ops bound available budget before height fits request
    as ⟨status,charged,values,accepted,same,appended⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  cases ty with
  | Bot =>
    simp only [runtime.compiler.stack_width, bind_ok]
    step as ⟨added,addSpec⟩
    cases added with
    | none => simp [compilerStackWidth] at slotsFit; scalar_tac
    | some next =>
      simp [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,compilerStackWidth,appended]
      scalar_tac
  | Val type =>
    simp only [runtime.compiler.stack_width]
    step with compiler_width type as ⟨width,widthEq⟩
    step as ⟨added,addSpec⟩
    cases added with
    | none =>
      simp only [compilerStackWidth] at slotsFit
      scalar_tac
    | some next =>
      simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
      exact ⟨trivial,trivial,appended,by simpa [compilerStackWidth,widthEq] using addSpec.2.1⟩

private theorem stack_width_le_two (ty : Itasca.code.StackType) : compilerStackWidth ty ≤ 2 := by
  cases ty with
  | Bot => decide
  | Val type => cases type <;> decide

/-- Rebuilding the remaining observed stack accepts under conservative
independent two-slots-per-value and one-entry-per-value bounds. This includes
polymorphic bottom values in unreachable code. -/
theorem observe_values_available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (budget : runtime.compiler.Budget A) (before : alloc.vec.Vec U32) (height : U32)
    (values : Slice Itasca.code.StackType) (index : Usize)
    (inside : index.val ≤ values.val.length)
    (capacity : before.length + (values.val.length-index.val) ≤ Usize.max)
    (request : before.length + (values.val.length-index.val) ≤ bound)
    (slotsFit : height.val + 2*(values.val.length-index.val) ≤ U32.max) :
    runtime.compiler.observe_values_loop ops budget before height values index (.Ok ()) ⦃ out =>
      out.1 = .Ok () ∧ out.2.1 = budget ∧
      out.2.2.1.length = before.length + (values.val.length-index.val) ∧
      out.2.2.2.val ≤ height.val + 2*(values.val.length-index.val) ⦄ := by
  unfold runtime.compiler.observe_values_loop
  apply loop.spec_decr_nat (fun state => values.val.length-state.2.2.2.1.val)
    (fun state => state.1 = budget ∧ state.2.2.2.2 = .Ok () ∧
      state.2.2.2.1.val ≤ values.val.length ∧
      state.2.1.length + (values.val.length-state.2.2.2.1.val) =
        before.length + (values.val.length-index.val) ∧
      state.2.2.1.val + 2*(values.val.length-state.2.2.2.1.val) ≤
        height.val + 2*(values.val.length-index.val))
  · rintro ⟨charged,offsets,current,next,status⟩ ⟨same,accepted,position,count,words⟩
    dsimp only at same accepted position count words
    subst charged status
    unfold runtime.compiler.observe_values_loop.body
    dsimp only
    split
    · rename_i more
      have atValue : next.val < values.val.length := by scalar_tac
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step as ⟨ty,found⟩
      have widthBound := stack_width_le_two ty
      step with observe_value_available ops bound available budget offsets current ty
        (by omega) (by omega) (by omega)
        as ⟨status,charged,after,afterHeight,accepted,same,appended,advanced⟩
      subst status charged
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_⟩
      · scalar_tac
      · simp only [alloc.vec.Vec.length] at count
        simp only [alloc.vec.Vec.length,appended,List.length_append,List.length_singleton]
        omega
      · omega
      · scalar_tac
    · have last : next.val = values.val.length := by scalar_tac
      simp [last]
      exact ⟨by simpa [last] using count,by simpa [last] using words⟩
  · exact ⟨rfl,rfl,inside,rfl,by dsimp only; omega⟩

end Itasca.Runtime.Compiler
