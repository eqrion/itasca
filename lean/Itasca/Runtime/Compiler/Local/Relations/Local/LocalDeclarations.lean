import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
/-! Exact allocation-aware local declaration accumulation and prefix offsets.
The actual function-start loop terminates with an explicit compiler error or
with every declared local represented at its source-order slot position. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.add_local.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.wasm_types.ValueType)
    (offsetsFit : compiler.local_offsets.val.length < Usize.max)
    (localsFit : compiler.function.locals.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler ty ⦃ out =>
      out.1 = .Ok () → ∃ budget count locals offsets,
        out.2 = { compiler with budget, function := { compiler.function with
          locals, local_slots := count }, local_offsets := offsets } ∧
        locals.val = compiler.function.locals.val ++ [ty] ∧
        offsets.val = compiler.local_offsets.val ++ [compiler.function.local_slots] ∧
        count.val = compiler.function.local_slots.val + width (Itasca.Translate.valueType ty) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.add_local
  step with charge_local ops compiler.budget as ⟨status, budget⟩
  cases status with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with budget_push ops law budget compiler.local_offsets compiler.function.local_slots offsetsFit
      as ⟨status, budget1, offsets, pushed⟩
    rcases pushed with ⟨rfl, rfl, offsetAppend⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law budget1 compiler.function.locals ty localsFit
        as ⟨status, budget2, locals, pushed⟩
      rcases pushed with ⟨rfl, rfl, localAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        step with compiler_width ty as ⟨word, exactWidth⟩
        step as ⟨count, countEq⟩
        cases count with
        | none => simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | some count =>
          simp only [core.option.Option.ok_or, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
            WP.spec_ok]
          intro accepted
          refine ⟨budget2, count, locals, offsets, rfl, localAppend, offsetAppend, ?_⟩
          simp_all
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem compiler_add_local {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.wasm_types.ValueType)
    (offsetsFit : compiler.local_offsets.val.length < Usize.max)
    (localsFit : compiler.function.locals.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler ty ⦃ out =>
      out.1 = .Ok () → ∃ budget count locals offsets,
        out.2 = { compiler with budget, function := { compiler.function with
          locals, local_slots := count }, local_offsets := offsets } ∧
        locals.val = compiler.function.locals.val ++ [ty] ∧
        offsets.val = compiler.local_offsets.val ++ [compiler.function.local_slots] ∧
        count.val = compiler.function.local_slots.val + width (Itasca.Translate.valueType ty) ⦄ := by
  exact runtime.compiler.FunctionCompiler.add_local.total ops law compiler ty offsetsFit localsFit

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.add_local.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (type : Itasca.wasm_types.ValueType)
    (room : compiler.budget.locals.val < compiler.budget.limits.max_locals.val)
    (localsCapacity : compiler.function.locals.length < Usize.max)
    (localsRequest : compiler.function.locals.length + 1 ≤ bound)
    (offsetCapacity : compiler.local_offsets.length < Usize.max)
    (offsetRequest : compiler.local_offsets.length + 1 ≤ bound)
    (slots : compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ≤ U32.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler type ⦃ out =>
      out.1 = .Ok () ∧ ∃ locals offsets localSlots used,
        out.2 = {compiler with
          budget := {compiler.budget with locals := used}
          function := {compiler.function with locals,local_slots := localSlots}
          local_offsets := offsets} ∧
        locals.val = compiler.function.locals.val ++ [type] ∧
        offsets.val = compiler.local_offsets.val ++ [compiler.function.local_slots] ∧
        localSlots.val = compiler.function.local_slots.val + width (Itasca.Translate.valueType type) ∧
        used.val = compiler.budget.locals.val + 1 ⦄ := by
  unfold runtime.compiler.FunctionCompiler.add_local
  step with charge_counter_available ops .locals compiler.budget room
    as ⟨status,charged,accepted,used,same,usedEq⟩
  rw [accepted]
  subst charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.local_offsets compiler.function.local_slots offsetCapacity offsetRequest
    as ⟨status,charged,offsets,accepted,same,appendedOffsets⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with budget_push_available ops bound available {compiler.budget with locals := used}
    compiler.function.locals type localsCapacity localsRequest
    as ⟨status,charged,locals,accepted,same,appendedLocals⟩
  subst status charged
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_ok]
  step with compiler_width type as ⟨word,wordEq⟩
  step as ⟨added,addSpec⟩
  cases added with
  | none => scalar_tac
  | some localSlots =>
    simp only [core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_ok,WP.spec_ok]
    exact ⟨trivial,locals,offsets,localSlots,used,rfl,appendedLocals,appendedOffsets,by scalar_tac,usedEq⟩

theorem local_offsets_append (types : List valtype) (ty : valtype) :
    (List.range (types ++ [ty]).length).map (offset (types ++ [ty])) =
      (List.range types.length).map (offset types) ++ [slots types] := by
  simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro index member
    have bound : index ≤ types.length := by have := List.mem_range.mp member; omega
    simp [offset, List.take_append_of_le_length bound]
  · simp [offset]

/-- State fields unrelated to declaration accumulation retain their original values. -/
def LocalFrame {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  after = { before with budget := after.budget, function := { before.function with locals := after.function.locals, local_slots := after.function.local_slots }, local_offsets := after.local_offsets }

structure LocalLayout {A : Type} (compiler : runtime.compiler.FunctionCompiler A) : Prop where
  slots : compiler.function.local_slots.val = Compiler.slots (compilerLocals compiler)
  offsets : compiler.local_offsets.val.map (fun word => word.val) =
    (List.range (compilerLocals compiler).length).map (offset (compilerLocals compiler))

theorem LocalFrame.refl {A : Type} (compiler : runtime.compiler.FunctionCompiler A) :
    LocalFrame compiler compiler := rfl

theorem LocalFrame.trans {A : Type} {a b c : runtime.compiler.FunctionCompiler A}
    (first : LocalFrame a b) (second : LocalFrame b c) : LocalFrame a c := by
  unfold LocalFrame at *
  rw [first] at second
  exact second

open Itasca.ResultFacts in
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.add_local.inv {A : Type}
    (ops : runtime.platform.Alloc A) (before after : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.wasm_types.ValueType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.add_local ops before ty = .ok (status, after)) :
    LocalFrame before after := by
  unfold runtime.compiler.FunctionCompiler.add_local at accepted
  obtain ⟨⟨charged, budget⟩, _, rest⟩ := bind_ok_inv _ _ _ accepted
  cases charged with
  | Err error =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
    rw [← rest.2]
    rfl
  | Ok value =>
    simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
    obtain ⟨⟨pushed, budget, offsets⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
    cases pushed with
    | Err error =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
      rw [← rest.2]
      rfl
    | Ok value =>
      simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
      obtain ⟨⟨pushed, budget, locals⟩, _, rest⟩ := bind_ok_inv _ _ _ rest
      cases pushed with
      | Err error =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
        rw [← rest.2]
        rfl
      | Ok value =>
        simp only [uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch, bind_ok] at rest
        obtain ⟨width, _, rest⟩ := bind_ok_inv _ _ _ rest
        obtain ⟨count, _, rest⟩ := bind_ok_inv _ _ _ rest
        cases count with
        | none =>
          simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, bind_ok, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          rw [← rest.2]
          rfl
        | some count =>
          simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            bind_ok, Result.ok.injEq, Prod.mk.injEq] at rest
          rw [← rest.2]
          rfl

@[step] theorem compiler_add_local_layout {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.wasm_types.ValueType) (layout : LocalLayout compiler)
    (fits : compiler.function.locals.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.add_local ops compiler ty ⦃ out =>
      out.1 = .Ok () → LocalFrame compiler out.2 ∧ LocalLayout out.2 ∧
        out.2.function.locals.val = compiler.function.locals.val ++ [ty] ⦄ := by
  have count := congrArg List.length layout.offsets
  have offsetsFit : compiler.local_offsets.val.length < Usize.max := by
    simp only [List.length_map, List.length_range, compilerLocals] at count
    simpa only [List.length_map] using count.trans_lt fits
  step with compiler_add_local ops law compiler ty offsetsFit fits
    as ⟨out, effect⟩
  rename_i accepted
  rcases out with ⟨status, updated⟩
  dsimp only at effect accepted ⊢
  obtain ⟨budget, count, locals, offsets, rfl, appended, offsetAppend, exactCount⟩ := effect accepted
  refine ⟨rfl, ⟨?_, ?_⟩, appended⟩
  · simp only [compilerLocals, appended, List.map_append, List.map_singleton,
      slots_append, slots, Nat.add_zero]
    simpa [compilerLocals, layout.slots] using exactCount
  · simp only [offsetAppend, List.map_append, List.map_singleton, compilerLocals,
      appended, local_offsets_append]
    simpa [compilerLocals, List.map_append, List.map_singleton, local_offsets_append,
      layout.slots] using congrArg (fun xs => xs ++ [slots (compilerLocals compiler)]) layout.offsets

def localLoopOutput {A : Type} (compiler : runtime.compiler.FunctionCompiler A)
    (status : core.result.Result Unit Itasca.error.VisitError) :=
  (compiler.signatures, compiler.func_param_slots, compiler.budget, compiler.batch_start,
    compiler.function, compiler.frames, compiler.reachable, compiler.next_source,
    compiler.before, compiler.height, compiler.local_offsets, compiler.table_depths, status)

open Itasca.ResultFacts in
theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.inv
    {A : Type} (ops : runtime.platform.Alloc A)
    (before : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context)
    (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError) {output}
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops before ctx index status = .ok output) :
    ∃ after result, output = localLoopOutput after result ∧ LocalFrame before after := by
  generalize measure : Usize.max - index.val = n
  induction n using Nat.strong_induction_on generalizing before index status with
  | h n ih =>
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop at accepted
    rw [loop] at accepted
    simp only [runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
      bind_ok] at accepted
    split at accepted
    · cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, Result.ok.injEq] at accepted
        subst output
        exact ⟨before, .Err error, rfl, .refl before⟩
      | Ok unit =>
        cases unit
        simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, Std.bind_assoc] at accepted
        obtain ⟨site, _, rest⟩ := bind_ok_inv _ _ _ accepted
        obtain ⟨⟨result, middle⟩, patched, tail⟩ := bind_ok_inv _ _ _ rest
        simp only [uncurry_apply_pair, Std.bind_assoc, bind_ok] at tail
        obtain ⟨nextIndex, increment, tail⟩ := bind_ok_inv _ _ _ tail
        have arithmetic := UScalar.add_equiv index 1#usize
        rw [increment] at arithmetic
        have progress : nextIndex.val = index.val + 1 := by simpa using arithmetic.2.1
        have nextMax := nextIndex.hmax
        have smaller : Usize.max - nextIndex.val < n := by scalar_tac
        have tail' : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
            ops middle ctx nextIndex result = .ok output := by
          simpa only [uncurry_apply_pair, bind_ok,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop,
            runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body,
            core.result.Result.is_ok] using tail
        obtain ⟨after, final, same, frame⟩ := ih _ smaller middle nextIndex result tail' rfl
        exact ⟨after, final, same,
          (runtime.compiler.FunctionCompiler.add_local.inv ops before middle site result patched).trans frame⟩
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      exact ⟨before, status, rfl, .refl before⟩


theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.total {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (index : Usize)
    (bound : index.val ≤ ctx.locals.val.length)
    (layout : LocalLayout compiler)
    (prefixTypes : compiler.function.locals.val = ctx.locals.val.take index.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops compiler ctx index (.Ok ()) ⦃ out => ∃ updated status,
        out = localLoopOutput updated status ∧
        (status = .Ok () → LocalFrame compiler updated ∧ LocalLayout updated ∧
          updated.function.locals.val = ctx.locals.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
  apply loop.spec_decr_nat (fun p => ctx.locals.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ ctx.locals.val.length ∧
      (p.2.2 = .Ok () → LocalFrame compiler p.1 ∧ LocalLayout p.1 ∧
        p.1.function.locals.val = ctx.locals.val.take p.2.1.val))
  · rintro ⟨current, i, status⟩ ⟨hi, invariant⟩
    dsimp only at hi invariant
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body
    dsimp only
    split
    · rename_i more
      have hb : i.val < ctx.locals.val.length := by scalar_tac
      cases status with
      | Err error =>
        simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ite_false, WP.spec_ok]
        exact ⟨current, .Err error, rfl, by simp⟩
      | Ok value =>
        cases value
        obtain ⟨frame, localLayout, types⟩ := invariant rfl
        have length : current.function.locals.val.length = i.val := by
          rw [types, List.length_take, Nat.min_eq_left hi]
        have capacity := ctx.locals.property
        have fits : current.function.locals.val.length < Usize.max := by omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step as ⟨ty, typeEq⟩
        step with compiler_add_local_layout ops law current ty localLayout fits
          as ⟨answer, updated, effect⟩
        step as ⟨next, nextEq⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨nextFrame, nextLayout, appended⟩ := effect accepted
        refine ⟨frame.trans nextFrame, nextLayout, ?_⟩
        rw [appended, types, typeEq, nextEq, List.take_concat_get' ctx.locals.val i.val hb]
    · rename_i finished
      have finalIndex : i.val = ctx.locals.val.length := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨current, status, rfl, ?_⟩
      intro accepted
      simpa [finalIndex] using invariant accepted
  · exact ⟨bound, fun _ => ⟨.refl compiler, layout, prefixTypes⟩⟩
@[step] theorem compiler_locals_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (index : Usize)
    (bound : index.val ≤ ctx.locals.val.length)
    (layout : LocalLayout compiler)
    (prefixTypes : compiler.function.locals.val = ctx.locals.val.take index.val) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops compiler ctx index (.Ok ()) ⦃ out => ∃ updated status,
        out = localLoopOutput updated status ∧
        (status = .Ok () → LocalFrame compiler updated ∧ LocalLayout updated ∧
          updated.function.locals.val = ctx.locals.val) ⦄ := by
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.total
    ops law compiler ctx index bound layout prefixTypes

theorem _root_.Itasca.runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.available {A : Type} (ops : runtime.platform.Alloc A)
    (bound : Nat) (available : Platform.AllocationAvailable ops bound)
    (compiler : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context) (index : Usize)
    (inside : index.val ≤ ctx.locals.val.length)
    (room : compiler.budget.locals.val + (ctx.locals.val.length-index.val) ≤ compiler.budget.limits.max_locals.val)
    (localsCapacity : compiler.function.locals.length + (ctx.locals.val.length-index.val) ≤ Usize.max)
    (localsReserve : compiler.function.locals.length + (ctx.locals.val.length-index.val) ≤ bound)
    (offsetCapacity : compiler.local_offsets.length + (ctx.locals.val.length-index.val) ≤ Usize.max)
    (offsetReserve : compiler.local_offsets.length + (ctx.locals.val.length-index.val) ≤ bound)
    (slots : compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val) ≤ U32.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop ops compiler ctx index (.Ok ())
      ⦃ out => ∃ after, out = localLoopOutput after (.Ok ()) ∧ LocalFrame compiler after ∧
        after.budget = {compiler.budget with locals := after.budget.locals} ∧
        after.function.locals.length = compiler.function.locals.length + (ctx.locals.val.length-index.val) ∧
        after.local_offsets.length = compiler.local_offsets.length + (ctx.locals.val.length-index.val) ∧
        after.budget.locals.val = compiler.budget.locals.val + (ctx.locals.val.length-index.val) ∧
        after.function.local_slots.val ≤ compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val) ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
  apply loop.spec_decr_nat (fun state => ctx.locals.val.length-state.2.1.val)
    (fun state => LocalFrame compiler state.1 ∧
      state.1.budget = {compiler.budget with locals := state.1.budget.locals} ∧ state.2.2 = .Ok () ∧
      state.2.1.val ≤ ctx.locals.val.length ∧
      state.1.function.locals.length + (ctx.locals.val.length-state.2.1.val) =
        compiler.function.locals.length + (ctx.locals.val.length-index.val) ∧
      state.1.local_offsets.length + (ctx.locals.val.length-state.2.1.val) =
        compiler.local_offsets.length + (ctx.locals.val.length-index.val) ∧
      state.1.budget.locals.val + (ctx.locals.val.length-state.2.1.val) =
        compiler.budget.locals.val + (ctx.locals.val.length-index.val) ∧
      state.1.function.local_slots.val + 2*(ctx.locals.val.length-state.2.1.val) ≤
        compiler.function.local_slots.val + 2*(ctx.locals.val.length-index.val))
  · rintro ⟨current,next,status⟩ ⟨frame,budgetFrame,accepted,position,localCount,offsetCount,used,words⟩
    dsimp only at frame budgetFrame accepted position localCount offsetCount used words
    subst status
    have limits : current.budget.limits = compiler.budget.limits := congrArg (fun value => value.limits) budgetFrame
    unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop.body
    dsimp only
    split
    · rename_i more
      have atLocal : next.val < ctx.locals.val.length := by
        simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using more
      simp only [core.result.Result.is_ok,bind_ok,↓reduceIte]
      step as ⟨type,found⟩
      have widthBound : width (Itasca.Translate.valueType type) ≤ 2 := by cases type <;> decide
      step with runtime.compiler.FunctionCompiler.add_local.available ops bound available current type
        (by rw [limits]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        as ⟨status,after,accepted,locals,offsets,localSlots,charged,shape,appendedLocals,appendedOffsets,slotEq,chargedEq⟩
      subst status after
      have nextFrame : LocalFrame compiler {current with
          budget := {current.budget with locals := charged}
          function := {current.function with locals,local_slots := localSlots}
          local_offsets := offsets} := frame.trans rfl
      have nextBudget : {current.budget with locals := charged} = {compiler.budget with locals := charged} := by
        rw [budgetFrame]
      clear frame budgetFrame
      step as ⟨following,followingEq⟩
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
      · exact nextFrame
      · exact nextBudget
      · scalar_tac
      · simp only [alloc.vec.Vec.length,appendedLocals,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at localCount
        omega
      · simp only [alloc.vec.Vec.length,appendedOffsets,List.length_append,List.length_singleton]
        simp only [alloc.vec.Vec.length] at offsetCount
        omega
      · omega
      · omega
      · scalar_tac
    · rename_i stopped
      have last : next.val = ctx.locals.val.length := by
        have ended : ctx.locals.val.length ≤ next.val := by
          simpa [UScalar.lt_equiv,alloc.vec.Vec.len] using stopped
        omega
      exact WP.spec.ret ⟨current,rfl,frame,budgetFrame,by simpa [last] using localCount,
        by simpa [last] using offsetCount,by simpa [last] using used,by simpa [last] using words⟩
  · exact ⟨.refl _,rfl,rfl,inside,rfl,rfl,rfl,by dsimp only; omega⟩

end Itasca.Runtime.Compiler
