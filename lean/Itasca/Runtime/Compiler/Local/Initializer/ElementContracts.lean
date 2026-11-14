import Itasca.Runtime.Compiler.Local.Initializer.ElementLoopContracts

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts

def sourceElementOffset (segment : Itasca.metadata.Element) : Option Itasca.wasm_types.ConstExpr :=
  match segment.mode with
  | .Active _ expr => some expr
  | .Passive | .Declarative => none

theorem element_offset_found (env : Itasca.metadata.Env) (index : Usize)
    (segment : Itasca.metadata.Element) (found : env.elements.val[index.val]? = some segment) :
    runtime.compiler.initialize.element_offset env index = .ok (sourceElementOffset segment) := by
  unfold runtime.compiler.initialize.element_offset
  simp only [Itasca.metadata.Env.impl.elements, bind_ok]
  rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref] using found), bind_ok]
  unfold sourceElementOffset
  cases segment.mode <;> rfl

/-- The successfully collected values and published row preceding offset compilation. -/
structure InitializerElementPrefix {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize) where
  middle : runtime.compiler.ExecutableModule
  collected : runtime.compiler.Budget A
  charged : runtime.compiler.Budget A
  indices : alloc.vec.Vec Usize
  rows : alloc.vec.Vec (alloc.vec.Vec Usize)
  loopCalled : runtime.compiler.initialize.lower_element_loop ops before budget index
    (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, collected, indices, .Ok ())
  rowCalled : runtime.compiler.Budget.push ops collected middle.element_initializers indices =
    .ok (.Ok (), charged, rows)

def InitializerElementPrefix.result {A : Type} {ops : runtime.platform.Alloc A}
    {before : runtime.compiler.ExecutableModule} {budget : runtime.compiler.Budget A} {index : Usize}
    (stages : InitializerElementPrefix ops before budget index) : runtime.compiler.ExecutableModule :=
  {stages.middle with element_initializers := stages.rows}

/-- Every normally returned element initializer retains its exact completed stages,
including rows published before an offset error. -/
inductive InitializerElementEffect {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) (index : Usize) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop
  | loopRejected (middle charged indices error)
      (called : runtime.compiler.initialize.lower_element_loop ops before budget index
        (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, charged, indices, .Err error)) :
      InitializerElementEffect ops before budget index (.Err error) middle charged
  | rowRejected (middle collected charged indices rows error)
      (loopCalled : runtime.compiler.initialize.lower_element_loop ops before budget index
        (alloc.vec.Vec.new _) 0#usize (.Ok ()) = .ok (middle, collected, indices, .Ok ()))
      (rowCalled : runtime.compiler.Budget.push ops collected middle.element_initializers indices =
        .ok (.Err error, charged, rows)) :
      InitializerElementEffect ops before budget index (.Err error) {middle with element_initializers := rows} charged
  | absent (stages : InitializerElementPrefix ops before budget index) (status charged offsets)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok none)
      (called : runtime.compiler.Budget.push ops stages.charged stages.middle.element_offsets none =
        .ok (status, charged, offsets)) :
      InitializerElementEffect ops before budget index status {stages.result with element_offsets := offsets} charged
  | expressionRejected (stages : InitializerElementPrefix ops before budget index) (expr middle charged error)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok (some expr))
      (called : runtime.compiler.initialize.expression ops stages.result stages.charged expr .I32 =
        .ok (.Err error, middle, charged)) :
      InitializerElementEffect ops before budget index (.Err error) middle charged
  | present (stages : InitializerElementPrefix ops before budget index) (expr middle expressionBudget value status charged offsets)
      (read : runtime.compiler.initialize.element_offset stages.middle.module.env index = .ok (some expr))
      (expressionCalled : runtime.compiler.initialize.expression ops stages.result stages.charged expr .I32 =
        .ok (.Ok value, middle, expressionBudget))
      (called : runtime.compiler.Budget.push ops expressionBudget middle.element_offsets (some value) =
        .ok (status, charged, offsets)) :
      InitializerElementEffect ops before budget index status {middle with element_offsets := offsets} charged

theorem _root_.Itasca.runtime.compiler.initialize.lower_element.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (index : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower_element ops before budget index = .ok (status, after, afterBudget)) :
    InitializerElementEffect ops before budget index status after afterBudget := by
  unfold runtime.compiler.initialize.lower_element at called
  obtain ⟨⟨middle, collected, indices, loopStatus⟩, loopCalled, tail⟩ := bind_ok_inv _ _ _ called
  cases loopStatus with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .loopRejected middle collected indices error loopCalled
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨rowStatus, charged, rows⟩, rowCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases rowStatus with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .rowRejected middle collected charged indices rows error loopCalled rowCalled
    | Ok unitValue =>
      cases unitValue
      let stages : InitializerElementPrefix ops before budget index :=
        ⟨middle, collected, charged, indices, rows, loopCalled, rowCalled⟩
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        runtime.compiler.ExecutableModule.env.eq, bind_ok] at tail
      obtain ⟨offset, read, tail⟩ := bind_ok_inv _ _ _ tail
      cases offset with
      | none =>
        obtain ⟨⟨result, finalBudget, offsets⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .absent stages result finalBudget offsets read pushed
      | some expr =>
        obtain ⟨⟨expressionStatus, final, expressionBudget⟩, expressionCalled, tail⟩ := bind_ok_inv _ _ _ tail
        cases expressionStatus with
        | Err error =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .expressionRejected stages expr final expressionBudget error read expressionCalled
        | Ok value =>
          simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
          obtain ⟨⟨result, finalBudget, offsets⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact .present stages expr final expressionBudget value result finalBudget offsets read expressionCalled pushed

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower_element.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize) (segment : Itasca.metadata.Element)
    (found : m.module.env.elements.val[i.val]? = some segment)
    (space : initializerSize m + segment.init.val.length + 3 ≤ Usize.max) :
    runtime.compiler.initialize.lower_element ops m budget i ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + segment.init.val.length + 3 ⦄ := by
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_total ops law m budget i (alloc.vec.Vec.new _) 0#usize
    (.Ok ()) segment found (by simp) (by simp) (by simpa using (show initializerSize m + segment.init.val.length ≤ Usize.max by omega))
    as ⟨middle, b1, indices, status, same, size⟩
  change initializerSize middle ≤ initializerSize m + segment.init.val.length at size
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same]; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_push_total ops law b1 middle.element_initializers indices
      (by unfold initializerSize at size space; omega) as ⟨status, b2, rows, rowsBound⟩
    cases status with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
      exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        runtime.compiler.ExecutableModule.env.eq,
        Itasca.metadata.Module.impl.env, runtime.compiler.initialize.element_offset, Itasca.metadata.Env.impl.elements]
      try simp only [bind_ok]
      rw [initializer_slice_index _ _ segment (by simpa [alloc.vec.Vec.deref, same] using found), bind_ok]
      have room : initializerSize { middle with element_initializers := rows } + 2 ≤ Usize.max := by
        unfold initializerSize at *; dsimp at *; omega
      have middleSize : initializerSize { middle with element_initializers := rows } ≤
          initializerSize m + segment.init.val.length + 1 := by
        unfold initializerSize at *; dsimp at *; omega
      cases mode : segment.mode with
      | Active table offset =>
        simp only [mode, bind_ok]
        step with initializer_expression_total ops law { middle with element_initializers := rows }
          b2 offset .I32 (by omega) as ⟨status, final, b3, source, growth⟩
        cases status with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame, bind_ok, bind_tc_ok, WP.spec_ok]
          exact ⟨source.trans same, by omega⟩
        | Ok index =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_push_total ops law b3 final.element_offsets (some index)
            (by unfold initializerSize at room growth; omega) as ⟨status, b4, offsets, offsetsBound⟩
          exact ⟨source.trans same, by unfold initializerSize at *; dsimp at *; omega⟩
      | Passive | Declarative =>
        simp only [mode, bind_ok]
        step with initializer_push_total ops law b2 middle.element_offsets none
          (by unfold initializerSize at room; dsimp at room; omega) as ⟨status, b3, offsets, offsetsBound⟩
        exact ⟨same, by unfold initializerSize at *; dsimp at *; omega⟩

/-- Source typing and independent retained/scratch demand for one element mapping. -/
structure InitializerElementDemand {A : Type} (bound : Nat) (module : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize) (segment : Itasca.metadata.Element) where
  lookup : module.module.env.elements.val[index.val]? = some segment
  typed : ∀ expr ∈ segment.init.val, Itasca.ModuleConstants.Valid module.module.env expr
      (Itasca.ModuleConstants.referenceValueType segment.elem)
  offsetTyped : ∀ table offset, segment.mode = .Active table offset →
      Itasca.ModuleConstants.Valid module.module.env offset .I32
  instructions : budget.instructions.val + 2*segment.init.length + 2 ≤ budget.limits.max_instructions.val
  codeRequest : 2 ≤ bound
  reserve : initializerSize module + segment.init.length + 3 ≤ bound
  capacity : initializerSize module + segment.init.length + 3 ≤ Usize.max

theorem _root_.Itasca.runtime.compiler.initialize.lower_element.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (index : Usize) (segment : Itasca.metadata.Element)
    (demand : InitializerElementDemand bound module budget index segment) :
    runtime.compiler.initialize.lower_element ops module budget index ⦃ out =>
      out.1 = .Ok () ∧ out.2.2.instructions.val ≤ budget.instructions.val + 2*segment.init.length + 2 ∧
      out.2.2.limits = budget.limits ∧ out.2.1.module = module.module ∧
      initializerSize out.2.1 ≤ initializerSize module + segment.init.length + 3 ⦄ := by
  rcases demand with ⟨lookup, typed, offsetTyped, instructions, codeRequest, reserve, capacity⟩
  have initLength : segment.init.length = segment.init.val.length := rfl
  simp only [alloc.vec.Vec.length] at instructions reserve capacity ⊢
  unfold runtime.compiler.initialize.lower_element
  step with initializer_element_values_available ops bound available module budget (alloc.vec.Vec.new _) index
    0#usize segment lookup (by simp) typed (by simpa [alloc.vec.Vec.length] using (show
      budget.instructions.val + 2*segment.init.length ≤ budget.limits.max_instructions.val by omega)) codeRequest
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ bound by omega))
    (by simpa [alloc.vec.Vec.length] using (show initializerSize module + segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ Usize.max by omega))
    (by simpa [alloc.vec.Vec.length,alloc.vec.Vec.new] using
      (show segment.init.length ≤ bound by omega))
    as ⟨middle,charged,indices,status,accepted,same,limits,size,indexSize,used⟩
  rw [accepted]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  have sizeBound : initializerSize middle + 3 ≤ bound := by change initializerSize middle + 3 ≤ bound; omega
  have sizeCapacity : initializerSize middle + 3 ≤ Usize.max := by omega
  step with budget_push_available ops bound available charged middle.element_initializers indices
    (by simp only [initializerSize] at sizeCapacity; omega)
    (by simp only [initializerSize] at sizeBound; omega)
    as ⟨status,rowBudget,rows,accepted,sameBudget,appended⟩
  subst status rowBudget
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok,
    runtime.compiler.ExecutableModule.env.eq,Itasca.metadata.Module.impl.env]
  rw [same,element_offset_found module.module.env index segment lookup,bind_ok]
  have rowSize : initializerSize {middle with module := module.module, element_initializers := rows} = initializerSize middle + 1 := by
    simp only [initializerSize,appended,List.length_append,List.length_singleton]
    omega
  generalize offsetEq : sourceElementOffset segment = offset
  cases offset with
  | none =>
    step with budget_push_available ops bound available charged middle.element_offsets none
      (by simp only [initializerSize] at sizeCapacity; omega)
      (by simp only [initializerSize] at sizeBound; omega)
      as ⟨status,afterBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_⟩
    · simpa [sameBudget,used] using (show charged.instructions.val ≤ budget.instructions.val + 2*segment.init.length+2 by omega)
    · simpa [sameBudget] using limits
    · simp only [initializerSize,appended,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at size
      omega
  | some expr =>
    have valid : Itasca.ModuleConstants.Valid module.module.env expr .I32 := by
      unfold sourceElementOffset at offsetEq
      cases mode : segment.mode with
      | Passive => simp [mode] at offsetEq
      | Declarative => simp [mode] at offsetEq
      | Active table offset =>
        simp only [mode,Option.some.injEq] at offsetEq
        subst expr
        exact offsetTyped table offset mode
    have functionBound : middle.functions.length ≤ initializerSize middle := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with runtime.compiler.initialize.expression.available ops bound available {middle with module := module.module, element_initializers := rows} charged expr .I32
      (by intro lo hi matching; rw [matching] at valid; cases valid) (by rw [limits]; omega) codeRequest
      (by change middle.functions.length + 1 ≤ bound; omega)
      (by change middle.functions.length < Usize.max; omega)
      as ⟨status,afterExpression,afterBudget,accepted,usedAgain,limitsAgain,function,shape,emitted,sameExpression⟩
    rw [accepted]
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
    have expressionSize : initializerSize afterExpression = initializerSize middle + 2 := by
      rw [sameExpression]
      simp only [initializerSize,emitted,List.length_append,List.length_singleton] at rowSize ⊢
      omega
    have offsetBound : afterExpression.element_offsets.length ≤ initializerSize afterExpression := by
      simp only [initializerSize,alloc.vec.Vec.length]
      omega
    step with budget_push_available ops bound available afterBudget afterExpression.element_offsets _
      (by change afterExpression.element_offsets.length < Usize.max; omega)
      (by change afterExpression.element_offsets.length + 1 ≤ bound; omega)
      as ⟨status,finalBudget,offsets,accepted,sameBudget,mapped⟩
    refine ⟨accepted,?_,?_,?_,?_⟩
    · simpa [sameBudget] using (show afterBudget.instructions.val ≤ budget.instructions.val+2*segment.init.length+2 by omega)
    · simpa [sameBudget,limitsAgain] using limits
    · exact congrArg (fun value => value.module) sameExpression
    · simp only [initializerSize,mapped,List.length_append,List.length_singleton]
      simp only [initializerSize] at expressionSize size
      omega

/-- Normal element-value loop returns preserve the executable source module. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower_element_loop.source {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (indices outIndices : alloc.vec.Vec Usize)
    (i j : Usize) (status result : core.result.Result Unit Itasca.error.VisitError)
    (segment : Itasca.metadata.Element) (found : before.module.env.elements.val[i.val]? = some segment)
    (bounded : j.val ≤ segment.init.val.length)
    (called : runtime.compiler.initialize.lower_element_loop ops before budget i indices j status =
      .ok (after, afterBudget, outIndices, result)) : after.module = before.module := by
  apply runtime.compiler.initialize.lower_element_loop.inv
    { ops := ops, before := before, budget := budget, indices := indices, i := i, j := j,
      status := status, segment := segment, found := found, bounded := bounded,
      P := fun _ _ _ _ _ => True, Q := fun current _ _ _ => current.module = before.module,
      advance := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True.intro,
      finish := fun _ _ _ _ _ source _ _ _ => source, initial := True.intro }
    after afterBudget outIndices result called

/-- Even partial element publication preserves the executable source module. -/
theorem InitializerElementEffect.source {A : Type} {ops : runtime.platform.Alloc A}
    {before after : runtime.compiler.ExecutableModule} {budget afterBudget : runtime.compiler.Budget A}
    {index : Usize} {status : core.result.Result Unit Itasca.error.VisitError}
    (effect : InitializerElementEffect ops before budget index status after afterBudget)
    (segment : Itasca.metadata.Element) (found : before.module.env.elements.val[index.val]? = some segment) :
    after.module = before.module := by
  have loopSource : ∀ middle charged indices result,
      runtime.compiler.initialize.lower_element_loop ops before budget index (alloc.vec.Vec.new _) 0#usize (.Ok ()) =
        .ok (middle, charged, indices, result) → middle.module = before.module := by
    intro middle charged indices result called
    exact runtime.compiler.initialize.lower_element_loop.source ops before middle budget charged
      (alloc.vec.Vec.new _) indices index 0#usize (.Ok ()) result segment found (by change 0 ≤ _; omega) called
  cases effect with
  | loopRejected middle charged indices error called => exact loopSource after afterBudget indices (.Err error) called
  | rowRejected middle collected charged indices rows error called pushed =>
    exact loopSource middle collected indices (.Ok ()) called
  | absent stages status charged offsets read pushed =>
    exact loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled
  | expressionRejected stages expr middle charged error read called =>
    have expression := runtime.compiler.initialize.expression.inv ops stages.result after stages.charged afterBudget expr .I32 (.Err error) called
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) expression.frame
    exact source.trans (loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled)
  | present stages expr middle expressionBudget value status charged offsets read called pushed =>
    have expression := runtime.compiler.initialize.expression.inv ops stages.result middle stages.charged expressionBudget expr .I32 (.Ok value) called
    have source := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) expression.frame
    exact source.trans (loopSource stages.middle stages.collected stages.indices (.Ok ()) stages.loopCalled)

end Itasca.Runtime.Compiler
