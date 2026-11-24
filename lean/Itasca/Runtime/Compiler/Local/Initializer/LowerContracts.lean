import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Definitions
import Itasca.Runtime.Compiler.Local.Initializer.SegmentEmissionContracts

/-!
Proofs for Runtime / Compiler / Local / Initializer.

This module collects SegmentLoopContracts, LowerContracts.
Each section documents its contracts and consumers.
-/

/-! ## SegmentLoopContracts -/

section

/-!
# Segment emission traversal

The common indexed emission loop handles source element and data segments. Its status and state relations preserve the effects needed by whole-module initializer compilation.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

private abbrev SegmentStatus := core.result.Result Unit Itasca.error.VisitError
private abbrev SegmentState (A : Type) := runtime.compiler.Budget A × Usize × SegmentStatus × runtime.bytecode.CompiledFunction
private abbrev SegmentResult (A : Type) := runtime.compiler.Budget A × SegmentStatus × runtime.bytecode.CompiledFunction

/-- Common indexed emission traversal for source element and data segments. -/
structure InitializerSegmentLoop (A : Type) where
  body : SegmentState A → Result (ControlFlow (SegmentState A) (SegmentResult A))
  callback : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize →
    Result (SegmentStatus × runtime.compiler.Budget A × runtime.bytecode.CompiledFunction)
  count : Usize
  body_eq : ∀ budget cursor status function,
    body (budget, cursor, status, function) =
      if cursor < count then
        match status with
        | .Err _ => .ok (.done (budget, status, function))
        | .Ok () => do
          let (result, nextBudget, nextFunction) ← callback budget function cursor
          let nextIndex ← cursor + 1#usize
          Result.ok (.cont (nextBudget, nextIndex, result, nextFunction))
      else .ok (.done (budget, status, function))

/-- The state predicate and terminal projection for normal segment-loop returns. -/
structure SegmentLoopInvariant (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  status : SegmentStatus
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → SegmentStatus → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → SegmentStatus → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor (.Ok ()) →
    ∀ result nextBudget nextFunction (nextIndex : Usize),
      rules.callback charged current cursor = .ok (result, nextBudget, nextFunction) →
      nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex result
  finish : ∀ charged current cursor result, P charged current cursor result →
    (rules.count.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q charged current result
  initial : P budget function index status

theorem InitializerSegmentLoop.inv {A : Type} (context : SegmentLoopInvariant A)
    (afterBudget : runtime.compiler.Budget A) (after : runtime.bytecode.CompiledFunction) (result : SegmentStatus)
    (called : loop context.rules.body (context.budget, context.index, context.status, context.function) =
      .ok (afterBudget, result, after)) : context.Q afterBudget after result := by
  rcases context with ⟨rules, budget, function, index, status, P, Q, advance, finish, initial⟩
  let measure : SegmentState A → Nat := fun (_, cursor, _, _) => rules.count.val - cursor.val
  let invariant : SegmentState A → Prop := fun (charged, cursor, result, current) => P charged current cursor result
  apply initializer_loop_success _ measure invariant
    (fun (charged, result, current) => Q charged current result) ?_ _ initial _ called
  rintro ⟨charged, cursor, result, current⟩ prior flow body
  rw [rules.body_eq] at body
  by_cases more : cursor < rules.count
  · rw [if_pos more] at body
    have inside : cursor.val < rules.count.val := by scalar_tac
    cases result with
    | Err error =>
      have output := Result.ok_injective body
      subst flow
      exact finish charged current cursor (.Err error) prior (.inr (by intro impossible; cases impossible))
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨nextResult, nextBudget, nextFunction⟩, lowered, tail⟩ := bind_ok_inv _ _ _ body
      obtain ⟨nextIndex, added, tail⟩ := bind_ok_inv _ _ _ tail
      have output := Result.ok_injective tail
      subst flow
      have increment : cursor + 1#usize ⦃ next => next.val = cursor.val + 1 ⦄ := by
        step as ⟨next, nextEq⟩
        scalar_tac
      rw [added] at increment
      simp only [WP.spec_ok] at increment
      refine ⟨advance charged current cursor inside prior nextResult nextBudget nextFunction nextIndex lowered increment, ?_⟩
      dsimp only [measure]
      omega
  · rw [if_neg more] at body
    have output := Result.ok_injective body
    subst flow
    have last : rules.count.val ≤ cursor.val := by scalar_tac
    exact finish charged current cursor result prior (.inl last)

/-- Callback normality and a decreasing index certify complete loop normality. -/
structure SegmentLoopTotal (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  status : SegmentStatus
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → SegmentStatus → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → SegmentStatus → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor (.Ok ()) →
    rules.callback charged current cursor ⦃ (result, nextBudget, nextFunction) =>
      ∀ nextIndex, nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex result ⦄
  finish : ∀ charged current cursor result, P charged current cursor result →
    (rules.count.val ≤ cursor.val ∨ result ≠ .Ok ()) → Q charged current result
  initial : P budget function index status

@[step] theorem InitializerSegmentLoop.total {A : Type} (context : SegmentLoopTotal A) :
    loop context.rules.body (context.budget, context.index, context.status, context.function)
      ⦃ (afterBudget, result, after) => context.Q afterBudget after result ⦄ := by
  rcases context with ⟨rules, budget, function, index, status, P, Q, advance, finish, initial⟩
  let measure : SegmentState A → Nat := fun (_, cursor, _, _) => rules.count.val - cursor.val
  let invariant : SegmentState A → Prop := fun (charged, cursor, result, current) => P charged current cursor result
  apply loop.spec_decr_nat measure invariant
  · rintro ⟨charged, cursor, result, current⟩ prior
    rw [rules.body_eq]
    by_cases more : cursor < rules.count
    · rw [if_pos more]
      have inside : cursor.val < rules.count.val := by scalar_tac
      cases result with
      | Err error => exact WP.spec.ret (finish charged current cursor (.Err error) prior
          (.inr (by intro impossible; cases impossible)))
      | Ok unitValue =>
        cases unitValue
        obtain ⟨⟨nextResult, nextBudget, nextFunction⟩, lowered, post⟩ :=
          WP.spec_imp_exists (advance charged current cursor inside prior)
        simp only [lowered, bind_ok, uncurry_apply_pair]
        step as ⟨nextIndex, increment⟩
        refine ⟨post nextIndex (by scalar_tac), ?_⟩
        dsimp only [measure]
        scalar_tac
    · rw [if_neg more]
      have last : rules.count.val ≤ cursor.val := by scalar_tac
      exact WP.spec.ret (finish charged current cursor result prior (.inl last))
  · exact initial

/-- Successful segment callbacks yield a successful complete traversal. -/
structure SegmentLoopAvailable (A : Type) where
  rules : InitializerSegmentLoop A
  budget : runtime.compiler.Budget A
  function : runtime.bytecode.CompiledFunction
  index : Usize
  bounded : index.val ≤ rules.count.val
  P : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Usize → Prop
  Q : runtime.compiler.Budget A → runtime.bytecode.CompiledFunction → Prop
  advance : ∀ charged current cursor, cursor.val < rules.count.val → P charged current cursor →
    rules.callback charged current cursor ⦃ (result, nextBudget, nextFunction) => result = .Ok () ∧
      ∀ nextIndex, nextIndex.val = cursor.val + 1 → P nextBudget nextFunction nextIndex ⦄
  finish : ∀ charged current cursor, cursor.val = rules.count.val → P charged current cursor → Q charged current
  initial : P budget function index

@[step] theorem InitializerSegmentLoop.available {A : Type} (context : SegmentLoopAvailable A) :
    loop context.rules.body (context.budget, context.index, .Ok (), context.function)
      ⦃ (afterBudget, result, after) => result = .Ok () ∧ context.Q afterBudget after ⦄ := by
  rcases context with ⟨rules, budget, function, index, bounded, P, Q, advance, finish, initial⟩
  apply InitializerSegmentLoop.total
    { rules := rules, budget := budget, function := function, index := index, status := .Ok (),
      P := fun charged current cursor result => result = .Ok () ∧ cursor.val ≤ rules.count.val ∧ P charged current cursor,
      Q := fun charged current result => result = .Ok () ∧ Q charged current,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor inside prior
    apply WP.spec_mono (advance charged current cursor inside prior.2.2)
    rintro ⟨result, nextBudget, nextFunction⟩ ⟨accepted, post⟩ nextIndex increment
    exact ⟨accepted, by omega, post nextIndex increment⟩
  · intro charged current cursor result prior stopped
    have last := stopped.resolve_right (by intro rejected; exact rejected prior.1)
    exact ⟨prior.1, finish charged current cursor (by omega) prior.2.2⟩
  · exact ⟨rfl, bounded, initial⟩

/-- Indexed initialization-code emission for source element segments. -/
def initializerEmitElementLoop {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) : InitializerSegmentLoop A where
  body := fun (budget, cursor, status, function) =>
    runtime.compiler.initialize.lower_loop3.body ops module budget cursor status function
  callback := fun budget function cursor => runtime.compiler.initialize.emit_element ops module budget function cursor
  count := alloc.vec.Vec.len module.module.env.elements
  body_eq := by
    intro budget cursor status function
    unfold runtime.compiler.initialize.lower_loop3.body
    simp only [runtime.compiler.ExecutableModule.env.eq, Itasca.metadata.Env.impl.elements, bind_ok]
    have size : Slice.len module.module.env.elements.deref = alloc.vec.Vec.len module.module.env.elements := by
      simp only [alloc.vec.Vec.deref, Slice.len, alloc.vec.Vec.len, Slice.from_val]
    rw [size]
    cases status with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]

/-- Indexed initialization-code emission for source data segments. -/
def initializerEmitDataLoop {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) : InitializerSegmentLoop A where
  body := fun (budget, cursor, status, function) =>
    runtime.compiler.initialize.lower_loop4.body ops module budget cursor status function
  callback := fun budget function cursor => runtime.compiler.initialize.emit_data ops module budget function cursor
  count := alloc.vec.Vec.len module.module.tail.data
  body_eq := by
    intro budget cursor status function
    unfold runtime.compiler.initialize.lower_loop4.body
    simp only [runtime.compiler.ExecutableModule.tail.eq, bind_ok]
    cases status with
    | Err error => simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false]
    | Ok unitValue =>
      cases unitValue
      simp only [core.result.Result.is_ok, bind_ok, ite_true]

end Itasca.Compiler

end

/-! ## LowerContracts -/

section

/-!
# Complete initializer lowering

A proof-only factorization exposes the extracted suffix after read-only mappings. The contract retains actual errors, emitted segment code and source-ordered mapping evidence.
-/

namespace Itasca.Compiler
open Aeneas Aeneas.Std Itasca.Computation

/-- The exact extracted suffix after read-only initializer mappings. This is a
proof-only factorization of `initialize.lower`, retaining its actual error,
allocator, and publication branches. It adds no runtime API or external model. -/
def segmentCompilation {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    Result (core.result.Result Unit Itasca.error.VisitError × runtime.compiler.ExecutableModule ×
      runtime.compiler.Budget A) := do
  let function ←
    runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new
      _root_.Itasca.runtime.bytecode.Instr) 0#u32
  let (budget4, result3, function1) ←
    runtime.compiler.initialize.lower_loop3 ops module
      budget 0#usize (core.result.Result.Ok ()) function
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch result3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let (budget5, result4, function2) ←
      runtime.compiler.initialize.lower_loop4 ops module
        budget4 0#usize result3 function1
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch result4
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let (r, budget6, v) ←
        runtime.compiler.initialize.emit ops budget5
          function2.code (runtime.bytecode.Instr.Return 0#u32 0#u32)
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let b ←
          runtime.bytecode.CompiledFunction.well_formed
            { function2 with code := v }
        if b
        then
          let i := alloc.vec.Vec.len module.functions
          let (r1, budget7, v1) ←
            runtime.compiler.Budget.push ops budget6
              module.functions { function2 with code := v }
          .ok (r1, { module with functions := v1, initialization := i },
            budget7)
        else
          .ok (core.result.Result.Err
            _root_.Itasca.error.VisitError.OutOfMemory, module, budget6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r1 ←
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
            residual
        .ok (r1, module, budget6)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
          residual
      .ok (r, module, budget5)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
        Unit (core.convert.FromSame _root_.Itasca.error.VisitError)
        residual
    .ok (r, module, budget4)

/-- The three read-only mapping passes followed by the existing segment suffix. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower.eq {A : Type}
    (ops : runtime.platform.Alloc A) (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    runtime.compiler.initialize.lower ops module budget = (do
      let (globals, globalsBudget, status) ← runtime.compiler.initialize.lower_loop0 ops module budget 0#usize (.Ok ())
      match status with
      | .Err error => Result.ok (.Err error, globals, globalsBudget)
      | .Ok () =>
        let (elements, elementsBudget, status) ← runtime.compiler.initialize.lower_loop1 ops globals globalsBudget 0#usize (.Ok ())
        match status with
        | .Err error => Result.ok (.Err error, elements, elementsBudget)
        | .Ok () =>
          let (data, dataBudget, status) ← runtime.compiler.initialize.lower_loop2 ops elements elementsBudget 0#usize (.Ok ())
          match status with
          | .Err error => Result.ok (.Err error, data, dataBudget)
          | .Ok () => segmentCompilation ops data dataBudget) := by
  unfold runtime.compiler.initialize.lower
  congr 1
  funext (globals, globalsBudget, status)
  cases status with
  | Err error => simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, bind_ok, bind_tc_ok]
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    congr 1
    funext (elements, elementsBudget, status)
    cases status with
    | Err error => simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, bind_ok, bind_tc_ok]
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      congr 1
      funext (data, dataBudget, status)
      cases status with
      | Err error => simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from, bind_ok, bind_tc_ok]
      | Ok unitValue =>
        cases unitValue
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        rfl

/-- Exact successful calls for the three mapping passes. -/
structure InitializerMappingTrace {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) where
  globals : runtime.compiler.ExecutableModule
  elements : runtime.compiler.ExecutableModule
  data : runtime.compiler.ExecutableModule
  globalsBudget : runtime.compiler.Budget A
  elementsBudget : runtime.compiler.Budget A
  dataBudget : runtime.compiler.Budget A
  globalsCalled : runtime.compiler.initialize.lower_loop0 ops module budget 0#usize (.Ok ()) =
    .ok (globals, globalsBudget, .Ok ())
  elementsCalled : runtime.compiler.initialize.lower_loop1 ops globals globalsBudget 0#usize (.Ok ()) =
    .ok (elements, elementsBudget, .Ok ())
  dataCalled : runtime.compiler.initialize.lower_loop2 ops elements elementsBudget 0#usize (.Ok ()) =
    .ok (data, dataBudget, .Ok ())

/-- Mapping refusals retain their actual intermediate state; completion delegates
exactly to the existing segment-compilation suffix, including its errors. -/
inductive InitializerLowerEffect {A : Type} (ops : runtime.platform.Alloc A)
    (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A) :
    core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop
  | globalsRejected (globals charged error)
      (called : runtime.compiler.initialize.lower_loop0 ops module budget 0#usize (.Ok ()) = .ok (globals, charged, .Err error)) :
      InitializerLowerEffect ops module budget (.Err error) globals charged
  | elementsRejected (globals elements globalsBudget elementsBudget error)
      (globalsCalled : runtime.compiler.initialize.lower_loop0 ops module budget 0#usize (.Ok ()) = .ok (globals, globalsBudget, .Ok ()))
      (called : runtime.compiler.initialize.lower_loop1 ops globals globalsBudget 0#usize (.Ok ()) = .ok (elements, elementsBudget, .Err error)) :
      InitializerLowerEffect ops module budget (.Err error) elements elementsBudget
  | dataRejected (globals elements data globalsBudget elementsBudget dataBudget error)
      (globalsCalled : runtime.compiler.initialize.lower_loop0 ops module budget 0#usize (.Ok ()) = .ok (globals, globalsBudget, .Ok ()))
      (elementsCalled : runtime.compiler.initialize.lower_loop1 ops globals globalsBudget 0#usize (.Ok ()) = .ok (elements, elementsBudget, .Ok ()))
      (called : runtime.compiler.initialize.lower_loop2 ops elements elementsBudget 0#usize (.Ok ()) = .ok (data, dataBudget, .Err error)) :
      InitializerLowerEffect ops module budget (.Err error) data dataBudget
  | suffix (stages : InitializerMappingTrace ops module budget) (status after afterBudget)
      (called : segmentCompilation ops stages.data stages.dataBudget = .ok (status, after, afterBudget)) :
      InitializerLowerEffect ops module budget status after afterBudget

theorem _root_.Itasca.runtime.compiler.initialize.lower.inv {A : Type}
    (ops : runtime.platform.Alloc A) (module after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A) (status : core.result.Result Unit Itasca.error.VisitError)
    (called : runtime.compiler.initialize.lower ops module budget = .ok (status, after, afterBudget)) :
    InitializerLowerEffect ops module budget status after afterBudget := by
  rw [runtime.compiler.initialize.lower.eq] at called
  obtain ⟨⟨globals, globalsBudget, result⟩, globalsCalled, tail⟩ := bind_ok_inv _ _ _ called
  cases result with
  | Err error =>
    simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
    obtain ⟨rfl, rfl, rfl⟩ := tail
    exact .globalsRejected globals globalsBudget error globalsCalled
  | Ok unitValue =>
    cases unitValue
    obtain ⟨⟨elements, elementsBudget, result⟩, elementsCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
      obtain ⟨rfl, rfl, rfl⟩ := tail
      exact .elementsRejected globals elements globalsBudget elementsBudget error globalsCalled elementsCalled
    | Ok unitValue =>
      cases unitValue
      obtain ⟨⟨data, dataBudget, result⟩, dataCalled, tail⟩ := bind_ok_inv _ _ _ tail
      cases result with
      | Err error =>
        simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
        obtain ⟨rfl, rfl, rfl⟩ := tail
        exact .dataRejected globals elements data globalsBudget elementsBudget dataBudget error globalsCalled elementsCalled dataCalled
      | Ok unitValue =>
        cases unitValue
        exact .suffix ⟨globals, elements, data, globalsBudget, elementsBudget, dataBudget,
          globalsCalled, elementsCalled, dataCalled⟩ status after afterBudget tail

/-- The high source-typing proof supplies actual mapping calls and proves the
suffix contract internally; the composition introduces no public trace premise. -/
@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower.available {A : Type}
    (ops : runtime.platform.Alloc A) (module : runtime.compiler.ExecutableModule) (budget : runtime.compiler.Budget A)
    (stages : InitializerMappingTrace ops module budget)
    (Q : core.result.Result Unit Itasca.error.VisitError → runtime.compiler.ExecutableModule → runtime.compiler.Budget A → Prop)
    (suffix : segmentCompilation ops stages.data stages.dataBudget ⦃ (status, after, afterBudget) => Q status after afterBudget ⦄) :
    runtime.compiler.initialize.lower ops module budget ⦃ (status, after, afterBudget) => Q status after afterBudget ⦄ := by
  rw [runtime.compiler.initialize.lower.eq, stages.globalsCalled]
  simp only [bind_ok, uncurry_apply_pair]
  rw [stages.elementsCalled]
  simp only [bind_ok, uncurry_apply_pair]
  rw [stages.dataCalled]
  simp only [bind_ok, uncurry_apply_pair]
  exact suffix

/-- Successful suffix publication retains each emitted program and checker call. -/
structure InitializerPublication {A : Type} (ops : runtime.platform.Alloc A)
    (module after : runtime.compiler.ExecutableModule) (budget afterBudget : runtime.compiler.Budget A) where
  seed : runtime.bytecode.CompiledFunction
  elements : runtime.bytecode.CompiledFunction
  data : runtime.bytecode.CompiledFunction
  elementsBudget : runtime.compiler.Budget A
  dataBudget : runtime.compiler.Budget A
  returnBudget : runtime.compiler.Budget A
  code : alloc.vec.Vec runtime.bytecode.Instr
  functions : alloc.vec.Vec runtime.bytecode.CompiledFunction
  seedCalled : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed
  elementsCalled : runtime.compiler.initialize.lower_loop3 ops module budget 0#usize (.Ok ()) seed =
    .ok (elementsBudget, .Ok (), elements)
  dataCalled : runtime.compiler.initialize.lower_loop4 ops module elementsBudget 0#usize (.Ok ()) elements =
    .ok (dataBudget, .Ok (), data)
  returnCalled : runtime.compiler.initialize.emit ops dataBudget data.code (.Return 0#u32 0#u32) =
    .ok (.Ok (), returnBudget, code)
  checked : runtime.bytecode.CompiledFunction.well_formed {data with code := code} = .ok true
  pushed : runtime.compiler.Budget.push ops returnBudget module.functions {data with code := code} =
    .ok (.Ok (), afterBudget, functions)
  frame : after = {module with functions := functions, initialization := alloc.vec.Vec.len module.functions}

theorem segmentCompilation.success {A : Type} (ops : runtime.platform.Alloc A)
    (module after : runtime.compiler.ExecutableModule) (budget afterBudget : runtime.compiler.Budget A)
    (called : segmentCompilation ops module budget = .ok (.Ok (), after, afterBudget)) :
    Nonempty (InitializerPublication ops module after budget afterBudget) := by
  unfold segmentCompilation at called
  obtain ⟨seed, seedCalled, tail⟩ := bind_ok_inv _ _ _ called
  obtain ⟨⟨elementsBudget, result, elements⟩, elementsCalled, tail⟩ := bind_ok_inv _ _ _ tail
  cases result with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
  | Ok unitValue =>
    cases unitValue
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
    obtain ⟨⟨dataBudget, result, data⟩, dataCalled, tail⟩ := bind_ok_inv _ _ _ tail
    cases result with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
    | Ok unitValue =>
      cases unitValue
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
      obtain ⟨⟨result, returnBudget, code⟩, returnCalled, tail⟩ := bind_ok_inv _ _ _ tail
      cases result with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
      | Ok unitValue =>
        cases unitValue
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at tail
        obtain ⟨checked, checkCalled, tail⟩ := bind_ok_inv _ _ _ tail
        cases checked with
        | false => simp only [ite_false, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at tail
        | true =>
          simp only [ite_true] at tail
          obtain ⟨⟨result, charged, functions⟩, pushed, tail⟩ := bind_ok_inv _ _ _ tail
          simp only [uncurry_apply_pair, Result.ok.injEq, Prod.mk.injEq] at tail
          obtain ⟨rfl, rfl, rfl⟩ := tail
          exact ⟨⟨seed, elements, data, elementsBudget, dataBudget, returnBudget, code, functions,
            seedCalled, elementsCalled, dataCalled, returnCalled, checkCalled, pushed, rfl⟩⟩

/-- Every successful complete pass has all mapping and publication evidence. -/
theorem _root_.Itasca.runtime.compiler.initialize.lower.success {A : Type}
    (ops : runtime.platform.Alloc A) (module after : runtime.compiler.ExecutableModule)
    (budget afterBudget : runtime.compiler.Budget A)
    (called : runtime.compiler.initialize.lower ops module budget = .ok (.Ok (), after, afterBudget)) :
    ∃ stages : InitializerMappingTrace ops module budget,
      Nonempty (InitializerPublication ops stages.data after stages.dataBudget afterBudget) := by
  have effect := runtime.compiler.initialize.lower.inv ops module after budget afterBudget (.Ok ()) called
  cases effect with
  | suffix stages _status _after _afterBudget suffix =>
    exact ⟨stages, segmentCompilation.success ops stages.data after stages.dataBudget afterBudget suffix⟩

theorem initializer_element_cost_step (elements : List Itasca.metadata.Element)
    (index : Nat) (segment : Itasca.metadata.Element) (found : elements[index]? = some segment) :
    initializerElementCost (elements.drop index) = segment.init.val.length + 3 +
      initializerElementCost (elements.drop (index + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp found).1]
  have element := (List.getElem?_eq_some_iff.mp found).2
  simp [initializerElementCost, element]

@[step] theorem initializer_global_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.env.globals.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_global ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  let global := m.module.env.globals.val[index.val]'bound
  have found : m.module.env.globals.val[index.val]? = some global := List.getElem?_eq_getElem bound
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  have initializersFit : m.global_initializers.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.lower_global.total ops law m budget index global found functionsFit initializersFit)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.lower_global.inv_selected ops m after budget afterBudget index global found status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

@[step] theorem initializer_data_offset_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (index : Usize)
    (bound : index.val < m.module.tail.data.val.length)
    (space : initializerSize m + 2 ≤ Usize.max) :
    runtime.compiler.initialize.lower_data_offset ops m budget index ⦃ out =>
      out.2.1.module = m.module ∧ initializerSize out.2.1 ≤ initializerSize m + 2 ⦄ := by
  let segment := m.module.tail.data.val[index.val]'bound
  have found : m.module.tail.data.val[index.val]? = some segment := List.getElem?_eq_getElem bound
  have functionsFit : m.functions.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  have offsetsFit : m.data_offsets.length < Usize.max := by
    simp only [initializerSize, alloc.vec.Vec.length] at space ⊢
    omega
  obtain ⟨⟨status, after, afterBudget⟩, called, normal⟩ := WP.spec_imp_exists
    (runtime.compiler.initialize.lower_data_offset.total ops law m budget index segment found functionsFit offsetsFit)
  rw [called]
  simp only [WP.spec_ok]
  have effect := runtime.compiler.initialize.lower_data_offset.inv_selected ops m after budget afterBudget index segment found status called
  have growth := effect.growth law
  have frame := effect.frame
  have moduleEq := congrArg (fun m : runtime.compiler.ExecutableModule => m.module) frame
  refine ⟨moduleEq, ?_⟩
  rw [frame]
  simp only [initializerSize]
  omega

@[step] theorem initializer_mapping_loop0_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop0 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.env.globals.val.length - i.val) ⦄ := by
  let P := fun current (_ : runtime.compiler.Budget A) (cursor : Usize) (_ : core.result.Result Unit Itasca.error.VisitError) =>
    initializerSize current + 2 * (m.module.env.globals.val.length - cursor.val) ≤
      initializerSize m + 2 * (m.module.env.globals.val.length - i.val)
  change WP.spec (loop (initializerGlobalLoop ops).body (m, budget, i, status)) _
  apply InitializerModuleLoop.total
    { rules := initializerGlobalLoop ops, before := m, budget := budget, j := i, status := status,
      length := alloc.vec.Vec.len m.module.env.globals, lengthEq := rfl, P := P,
      Q := (fun after _ _ => after.module = m.module ∧ initializerSize after ≤
      initializerSize m + 2 * (m.module.env.globals.val.length - i.val)), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source inside prior
    change cursor.val < m.module.env.globals.val.length at inside
    have currentBound : cursor.val < current.module.env.globals.val.length := by
      simpa only [source] using inside
    apply WP.spec_mono (initializer_global_total ops law current charged cursor currentBound (by dsimp only [P] at prior; omega))
    rintro ⟨result, next, nextBudget⟩ ⟨same, growth⟩ nextIndex increment
    dsimp only at growth
    dsimp only [P] at prior ⊢
    omega
  · intro current charged cursor result source prior stopped
    exact ⟨source, by dsimp only [P] at prior; omega⟩
  · exact Nat.le_refl _

@[step] theorem initializer_mapping_loop2_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop2 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + 2 * (m.module.tail.data.val.length - i.val) ⦄ := by
  let P := fun current (_ : runtime.compiler.Budget A) (cursor : Usize) (_ : core.result.Result Unit Itasca.error.VisitError) =>
    initializerSize current + 2 * (m.module.tail.data.val.length - cursor.val) ≤
      initializerSize m + 2 * (m.module.tail.data.val.length - i.val)
  change WP.spec (loop (initializerDataOffsetLoop ops).body (m, budget, i, status)) _
  apply InitializerModuleLoop.total
    { rules := initializerDataOffsetLoop ops, before := m, budget := budget, j := i, status := status,
      length := alloc.vec.Vec.len m.module.tail.data, lengthEq := rfl, P := P,
      Q := (fun after _ _ => after.module = m.module ∧ initializerSize after ≤
      initializerSize m + 2 * (m.module.tail.data.val.length - i.val)), advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source inside prior
    change cursor.val < m.module.tail.data.val.length at inside
    have currentBound : cursor.val < current.module.tail.data.val.length := by
      simpa only [source] using inside
    apply WP.spec_mono (initializer_data_offset_total ops law current charged cursor currentBound (by dsimp only [P] at prior; omega))
    rintro ⟨result, next, nextBudget⟩ ⟨same, growth⟩ nextIndex increment
    dsimp only at growth
    dsimp only [P] at prior ⊢
    omega
  · intro current charged cursor result source prior stopped
    exact ⟨source, by dsimp only [P] at prior; omega⟩
  · exact Nat.le_refl _

@[step] theorem initializer_mapping_loop1_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (i : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (space : initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ≤ Usize.max) :
    runtime.compiler.initialize.lower_loop1 ops m budget i status ⦃ out =>
      out.1.module = m.module ∧
      initializerSize out.1 ≤ initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val) ⦄ := by
  let P := fun current (_ : runtime.compiler.Budget A) (cursor : Usize) (_ : core.result.Result Unit Itasca.error.VisitError) =>
    initializerSize current + initializerElementCost (m.module.env.elements.val.drop cursor.val) ≤
      initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val)
  change WP.spec (loop (initializerElementLoop ops).body (m, budget, i, status)) _
  apply InitializerModuleLoop.total
    { rules := initializerElementLoop ops, before := m, budget := budget, j := i, status := status,
      length := alloc.vec.Vec.len m.module.env.elements, lengthEq := rfl, P := P,
      Q := fun after _ _ => after.module = m.module ∧ initializerSize after ≤
        initializerSize m + initializerElementCost (m.module.env.elements.val.drop i.val),
      advance := ?_, finish := ?_, initial := ?_ }
  · intro current charged cursor source inside prior
    change cursor.val < m.module.env.elements.val.length at inside
    let segment := m.module.env.elements.val[cursor.val]'inside
    have found : m.module.env.elements.val[cursor.val]? = some segment := List.getElem?_eq_getElem inside
    have cost := initializer_element_cost_step _ _ _ found
    dsimp only [P] at prior
    apply WP.spec_mono (runtime.compiler.initialize.lower_element.total ops law current charged cursor segment
      (by simpa only [source] using found) (by omega))
    rintro ⟨result, next, nextBudget⟩ ⟨same, growth⟩ nextIndex increment
    dsimp only at growth
    dsimp only [P]
    rw [increment]
    omega
  · intro current charged cursor result source prior stopped
    exact ⟨source, by dsimp only [P] at prior; omega⟩
  · exact Nat.le_refl _

@[step] theorem initializer_segment_loop3_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    (pairFits : function.indirect.val.length + (m.module.env.elements.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop3 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.env.elements.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.env.elements.val.length - i.val) ∧
      out.2.2.indirect.val.length ≤ function.indirect.val.length + (m.module.env.elements.val.length - i.val) ⦄ := by
  let P := fun (_ : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) (_ : core.result.Result Unit Itasca.error.VisitError) =>
    current.code.val.length + 5*(m.module.env.elements.val.length-cursor.val) ≤
      function.code.val.length + 5*(m.module.env.elements.val.length-i.val) ∧
    current.v128_pool.val.length + (m.module.env.elements.val.length-cursor.val) ≤
      function.v128_pool.val.length + (m.module.env.elements.val.length-i.val) ∧
    current.indirect.val.length + (m.module.env.elements.val.length - cursor.val) ≤
      function.indirect.val.length + (m.module.env.elements.val.length - i.val)
  change WP.spec (loop (initializerEmitElementLoop ops m).body (budget, i, status, function)) _
  apply InitializerSegmentLoop.total
    { rules := initializerEmitElementLoop ops m, budget := budget, function := function, index := i, status := status,
      P := P, Q := fun _ after _ =>
        after.code.val.length ≤ function.code.val.length + 5*(m.module.env.elements.val.length-i.val) ∧
        after.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.env.elements.val.length-i.val) ∧ after.indirect.val.length ≤ function.indirect.val.length + (m.module.env.elements.val.length-i.val),
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor inside prior
    obtain ⟨code, pool, pairs⟩ := prior
    change cursor.val < m.module.env.elements.val.length at inside
    apply WP.spec_mono (runtime.compiler.initialize.emit_element.total ops law m charged current cursor inside
      (by omega) (by omega) (by omega))
    rintro ⟨result, nextBudget, next⟩ ⟨codeGrowth, poolGrowth, pairGrowth⟩ nextIndex increment
    exact ⟨by omega, by omega, by omega⟩
  · intro charged current cursor result prior stopped
    obtain ⟨code, pool, pairs⟩ := prior
    exact ⟨by omega, by omega, by omega⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

@[step] theorem initializer_segment_loop4_total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A) (function : runtime.bytecode.CompiledFunction)
    (i : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (codeFits : function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    (poolFits : function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ≤ Usize.max)
    :
    runtime.compiler.initialize.lower_loop4 ops m budget i status function ⦃ out =>
      out.2.2.code.val.length ≤ function.code.val.length + 5 * (m.module.tail.data.val.length - i.val) ∧
      out.2.2.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.tail.data.val.length - i.val) ∧
      out.2.2.indirect = function.indirect ⦄ := by
  let P := fun (_ : runtime.compiler.Budget A) (current : runtime.bytecode.CompiledFunction) (cursor : Usize) (_ : core.result.Result Unit Itasca.error.VisitError) =>
    current.code.val.length + 5*(m.module.tail.data.val.length-cursor.val) ≤
      function.code.val.length + 5*(m.module.tail.data.val.length-i.val) ∧
    current.v128_pool.val.length + (m.module.tail.data.val.length-cursor.val) ≤
      function.v128_pool.val.length + (m.module.tail.data.val.length-i.val) ∧
    current.indirect = function.indirect
  change WP.spec (loop (initializerEmitDataLoop ops m).body (budget, i, status, function)) _
  apply InitializerSegmentLoop.total
    { rules := initializerEmitDataLoop ops m, budget := budget, function := function, index := i, status := status,
      P := P, Q := fun _ after _ =>
        after.code.val.length ≤ function.code.val.length + 5*(m.module.tail.data.val.length-i.val) ∧
        after.v128_pool.val.length ≤ function.v128_pool.val.length + (m.module.tail.data.val.length-i.val) ∧ after.indirect = function.indirect,
      advance := ?_, finish := ?_, initial := ?_ }
  · intro charged current cursor inside prior
    obtain ⟨code, pool, pairs⟩ := prior
    change cursor.val < m.module.tail.data.val.length at inside
    apply WP.spec_mono (runtime.compiler.initialize.emit_data.total ops law m charged current cursor inside
      (by omega) (by omega))
    rintro ⟨result, nextBudget, next⟩ ⟨codeGrowth, poolGrowth, pairGrowth⟩ nextIndex increment
    exact ⟨by omega, by omega, pairGrowth.trans pairs⟩
  · intro charged current cursor result prior stopped
    obtain ⟨code, pool, pairs⟩ := prior
    exact ⟨by omega, by omega, pairs⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩

@[step] theorem _root_.Itasca.runtime.compiler.initialize.lower.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (m : runtime.compiler.ExecutableModule)
    (budget : runtime.compiler.Budget A)
    (mapSpace : initializerSize m + initializerMappingCost m.module + 1 ≤ Usize.max)
    (segmentSpace : 5 * (m.module.env.elements.val.length + m.module.tail.data.val.length) + 1 ≤ Usize.max) :
    runtime.compiler.initialize.lower ops m budget ⦃ out =>
      out.2.1.module = m.module ∧
      initializerSize out.2.1 ≤ initializerSize m + initializerMappingCost m.module + 1 ⦄ := by
  let seed := { initializerSeed .I32 with slot_count := 0#u32 }
  have seedEq : runtime.bytecode.CompiledFunction.synthetic (alloc.vec.Vec.new _) 0#u32 = .ok seed := rfl
  unfold runtime.compiler.initialize.lower
  step with initializer_mapping_loop0_total ops law m budget 0#usize (.Ok ())
    (by simp only [initializerMappingCost] at mapSpace; simp; omega)
    as ⟨m1, b1, status, source1, size1⟩
  simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero] at size1
  cases status with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, source1]
    unfold initializerMappingCost; omega
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with initializer_mapping_loop1_total ops law m1 b1 0#usize (.Ok value)
      (by simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1]; unfold initializerMappingCost at mapSpace; omega)
      as ⟨m2, b2, status, source2, size2⟩
    have same2 : m2.module = m.module := source2.trans source1
    simp only [show (0#usize).val = 0 from rfl, List.drop_zero, source1] at size2
    cases status with
    | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same2]
      unfold initializerMappingCost; omega
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with initializer_mapping_loop2_total ops law m2 b2 0#usize (.Ok value)
        (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2]; unfold initializerMappingCost at mapSpace; omega)
        as ⟨m3, b3, status, source3, size3⟩
      have same3 : m3.module = m.module := source3.trans same2
      simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same2] at size3
      have sizeBound : initializerSize m3 ≤ initializerSize m + initializerMappingCost m.module := by
        unfold initializerMappingCost; omega
      cases status with
      | Err error =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
        omega
      | Ok value =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        rw [seedEq, bind_ok]
        step with initializer_segment_loop3_total ops law m3 b3 seed 0#usize (.Ok value)
          (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega) (by simp [seed, initializerSeed, same3] <;> omega)
          as ⟨b4, status, function1, code1, pool1, pairs1⟩
        simp [seed, initializerSeed, same3] at code1 pool1 pairs1
        cases status with
        | Err error =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
          omega
        | Ok value =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with initializer_segment_loop4_total ops law m3 b4 function1 0#usize (.Ok value)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            (by simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3]; omega)
            as ⟨b5, status, function2, code2, pool2, pairs2⟩
          simp only [show (0#usize).val = 0 from rfl, Nat.sub_zero, same3] at code2
          cases status with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
            omega
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with initializer_emit_total ops law b5 function2.code _ (by omega)
              as ⟨status, b6, finalCode, codeCount⟩
            cases status with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, same3]
              omega
            | Ok value =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step with well_formed_total { function2 with code := finalCode } as ⟨valid⟩
              cases valid with
              | false => simp [same3]; omega
              | true =>
                simp only [↓reduceIte]
                step with initializer_push_total ops law b6 m3.functions _
                  (by unfold initializerSize at sizeBound mapSpace; omega)
                  as ⟨status, b7, functions, count⟩
                exact ⟨same3, by unfold initializerSize at *; dsimp at *; omega⟩

end Itasca.Compiler

end
