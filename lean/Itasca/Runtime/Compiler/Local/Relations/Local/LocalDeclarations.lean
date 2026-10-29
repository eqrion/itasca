import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Runtime.Compiler.Local.Relations.Layout.CompileInv
/-! Exact allocation-aware local declaration accumulation and prefix offsets.
The actual function-start loop terminates with an explicit compiler error or
with every declared local represented at its source-order slot position. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std
@[step] theorem charge_local {A : Type} (ops : runtime.platform.Alloc A)
    (budget : runtime.compiler.Budget A) :
    runtime.compiler.Budget.charge ops budget .Locals ⦃ out => True ⦄ := by
  simp only [runtime.compiler.Budget.charge]
  split
  · simp [runtime.compiler.Budget.reject, WP.spec_ok]
  · step

@[step] theorem compiler_add_local {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.types.ValueType)
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

@[step] theorem compiler_add_local_layout {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.types.ValueType) (layout : LocalLayout compiler)
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
end Itasca.Runtime.Compiler
