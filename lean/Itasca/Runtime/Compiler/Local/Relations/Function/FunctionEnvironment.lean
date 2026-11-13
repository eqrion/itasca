import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Support.ControlTranslation
import Itasca.Runtime.Representation.Values
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Source.SourceLengthsTactic

/-!
Sections, each formerly its own module: Signatures, FunctionEntry, FunctionEnvironment.
-/

/-! ## Signatures -/

section

/-! Compiler signature capture: total exact word counting, retained source
value/word arities, and source block-signature resolution. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

def signatureSlots (types : List Itasca.wasm_types.ValueType) : Nat :=
  slots (types.map Itasca.Translate.valueType)

theorem signature_slots_eq (types : List Itasca.wasm_types.ValueType) :
    signatureSlots types = Interp.valueTypeSlots types := by
  have same : Itasca.Translate.valueType = Interp.sourceType := by
    funext ty
    cases ty <;> rfl
  simp [signatureSlots, Interp.valueTypeSlots, same]

@[step] theorem compiler_type_slots (types : Slice Itasca.wasm_types.ValueType) :
    runtime.compiler.type_slots types ⦃ result =>
      match result with
      | .Ok word => word.val = signatureSlots types.val
      | .Err error => error = .Host ∧ U32.max < signatureSlots types.val ⦄ := by
  unfold runtime.compiler.type_slots
  step with Interp.value_type_slots types as ⟨slots, hs⟩
  rw [← signature_slots_eq] at hs
  have maxCast : (UScalar.cast .Usize core.num.U32.MAX).val = U32.max := by
    simp [core.num.U32.MAX, U32.rMax, U32.max, U32.numBits]
  cases slots with
  | none =>
    simp only at hs
    simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    scalar_tac
  | some total =>
    simp only at hs
    simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
    split
    · simp only [WP.spec_ok]
      exact ⟨trivial, by scalar_tac⟩
    · simp only [WP.spec_ok]
      rw [UScalar.cast_val_eq]
      scalar_tac

structure SignatureMatches (signature : runtime.compiler.Signature)
    (params results : List valtype) : Prop where
  parameters : signature.params.val = params.length
  resultArity : signature.results.val = results.length
  paramWords : signature.param_slots.val = slots params
  resultWords : signature.result_slots.val = slots results

def SignatureTable (signatures : Slice runtime.compiler.Signature) (types : List functype) : Prop :=
  ∀ (i : Nat) (signature : runtime.compiler.Signature), signatures.val[i]? = some signature →
    ∃ params results : List valtype, types[i]? = some (.mk_functype (.mk_list params) (.mk_list results)) ∧
      SignatureMatches signature params results

/-- Capturing an accepted module type appends its exact value and word counts.
The slot accumulator is total, and rejects only a width above the u32 bound. -/
@[step] theorem capture_signature {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (ty : Itasca.wasm_types.FuncType)
    (lookup : env.types.val[index.val]? = some ty)
    (fits : scheduler.signatures.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_signature ops scheduler env index ⦃ out =>
      out.1 = .Ok () → ∃ signature budget,
        out.2 = { scheduler with signatures := out.2.signatures, budget } ∧
        out.2.signatures.val = scheduler.signatures.val ++ [signature] ∧
        SignatureMatches signature (ty.params.val.map Itasca.Translate.valueType)
          (ty.results.val.map Itasca.Translate.valueType) ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_signature
  simp only [Itasca.metadata.Env.impl.types, bind_ok]
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index.val < env.types.deref.length := by simpa [alloc.vec.Vec.deref] using bound
  step as ⟨actual, hactual⟩
  have same : actual = ty := by
    simpa [List.getElem?_eq_getElem bound, alloc.vec.Vec.deref, hactual] using lookup
  rw [same]
  step with compiler_type_slots ty.params.deref as ⟨params, hparams⟩
  cases params with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok paramWords =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with compiler_type_slots ty.results.deref as ⟨results, hresults⟩
    cases results with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok resultWords =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with budget_push ops law scheduler.budget scheduler.signatures
        ⟨alloc.vec.Vec.len ty.params, alloc.vec.Vec.len ty.results, paramWords, resultWords⟩ fits
        as ⟨status, budget, signatures, pushed⟩
      rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [runtime.compiler.visitor_result, bind_ok, WP.spec_ok]
        intro accepted
        refine ⟨_, scheduler.budget, rfl, appended, ?_⟩
        constructor
        · simp [alloc.vec.Vec.len]
        · simp [alloc.vec.Vec.len]
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hparams
        · simpa [signatureSlots, alloc.vec.Vec.deref] using hresults
      · simp [runtime.compiler.visitor_result]
end Itasca.Runtime.Compiler

end

/-! ## FunctionEntry -/

section

/-!
The successful function-start callback establishes the zero-operand layout, source coordinates, and the root control frame used by all later callbacks.

Main declarations: `compiler_function_start` and `compiler_new`. A direct consumer is `Compiler.Module.CompileEntry`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The successful function-start callback establishes the zero-operand layout,
source coordinates, and the root control frame used by all later callbacks. -/
@[step] theorem compiler_function_start {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (compiler : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (signature : runtime.compiler.Signature)
    (bodyBegin bodyEnd : Usize)
    (lookup : compiler.signatures.val[typeIndex.val]? = some signature)
    (beginFits : compiler.batch_start.val + bodyBegin.val ≤ Usize.max)
    (endFits : compiler.batch_start.val + bodyEnd.val ≤ Usize.max)
    (emptyLocals : compiler.function.locals.val = [])
    (localLayout : LocalLayout compiler)
    (emptyOperands : compiler.before.val = [])
    (mapsFit : compiler.function.controls.val.length < Usize.max)
    (framesFit : compiler.frames.val.length < Usize.max) :
    runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops compiler ctx typeIndex bodyBegin bodyEnd ⦃ out =>
      out.1 = .Ok () → CompilerLayout out.2 [] ∧
        out.2.reachable = compiler.reachable ∧
        out.2.function.slot_count = out.2.function.local_slots ∧
        out.2.function.locals.val = ctx.locals.val ∧
        out.2.function.param_slots = signature.param_slots ∧
        out.2.function.type_index = typeIndex ∧
        out.2.function.body_start.val = compiler.batch_start.val + bodyBegin.val ∧
        out.2.function.body_end.val = compiler.batch_start.val + bodyEnd.val ∧
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = compiler.frames.val ++
          [⟨0#usize, .Body, out.2.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        out.2.function.controls.val = compiler.function.controls.val ++
          [⟨.Body, out.2.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize,
            0#usize, signature.results⟩] ⦄ := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
  step as ⟨start, startEq⟩
  step as ⟨finish, finishEq⟩
  step as ⟨index, indexEq⟩
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  step as ⟨sig, sigEq⟩
  have same : sig = signature := by simpa [indexEq, sigEq, List.getElem?_eq_getElem bound] using lookup
  rw [same]
  let initial := { compiler with function := { compiler.function with param_slots := signature.param_slots, type_index := typeIndex, body_start := start, body_end := finish } }
  have initialLayout : LocalLayout initial := ⟨localLayout.slots, localLayout.offsets⟩
  step with compiler_locals_loop ops law initial ctx 0#usize (by simp) initialLayout
    (by simpa [initial] using emptyLocals)
    as ⟨s, s1, b, i3, cf, v, b1, i4, v1, i5, v2, v3, result, updated, status, outputEq, certified⟩
  simp only [localLoopOutput, Prod.mk.injEq] at outputEq
  rcases outputEq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cases result with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok value =>
    cases value
    obtain ⟨frame, layout, types⟩ := certified rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    step with charge_control ops updated.budget as ⟨status, budget⟩
    cases status with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    | Ok value =>
      cases value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have sameControls : updated.function.controls = compiler.function.controls := by rw [frame]
      have sameFrames : updated.frames = compiler.frames := by rw [frame]
      step with budget_push ops law budget updated.function.controls
        ⟨.Body, updated.function.body_start, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, signature.results⟩
        (by simpa [sameControls] using mapsFit) as ⟨status, budget1, maps, pushed⟩
      rcases pushed with ⟨rfl, rfl, mapAppend⟩ | ⟨rfl, rfl, rejected⟩
      · simp only [bind_ok]
        step with budget_push ops law budget1 updated.frames
          ⟨0#usize, .Body, updated.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩
          (by simpa [sameFrames] using framesFit) as ⟨status, budget2, frames, pushed⟩
        rcases pushed with ⟨rfl, rfl, frameAppend⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [bind_ok, WP.spec_ok]
          intro accepted
          refine ⟨⟨layout.slots, layout.offsets, ?_, ?_, ?_⟩, ?_, True.intro, types, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have : updated.before = compiler.before := by rw [frame]
            simp [this, emptyOperands, stackOffsets]
          · simp only [compilerLocals, slots, Nat.add_zero]
            exact layout.slots
          · intro _; exact Nat.le_refl _
          · rw [frame]
          · rw [frame]
          · rw [frame]
          · rw [frame]; exact startEq
          · rw [frame]; exact finishEq
          · rw [frame]
          · simpa [sameFrames] using frameAppend
          · simpa [sameControls] using mapAppend
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

@[step] theorem compiler_new {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      LocalLayout out ∧ out.function.locals.val = [] ∧ out.before.val = [] ∧
        out.function.controls.val = [] ∧ out.frames.val = [] ∧
        out.function.code.val = [] ∧ out.reachable = true ∧
        out.signatures = signatures ∧ out.func_param_slots = functionSlots ∧
        out.batch_start = batchStart ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.new, WP.spec_ok]
  constructor
  · constructor <;> simp [compilerLocals, alloc.vec.Vec.new, slots]
  · simp [alloc.vec.Vec.new]
end Itasca.Runtime.Compiler

end

/-! ## FunctionEnvironment -/

section

/-!
Function entry and local declarations preserve the scheduler signature tables and batch origin.

Main declarations: `FunctionEnvironment`. A direct consumer is `Compiler.Body.Relations.Entry.FunctionStartFacts`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std Itasca.ResultFacts
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve the scheduler signature tables and batch origin. -/
def FunctionEnvironment {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.signatures, after.func_param_slots, after.batch_start) =
    (before.signatures, before.func_param_slots, before.batch_start)

theorem FunctionEnvironment.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : FunctionEnvironment before middle) (second : FunctionEnvironment middle after) :
    FunctionEnvironment before after := Eq.trans second first

open Lean Meta Elab Tactic in
elab "environment_frame_effect " h:ident " using " ops:term ", " law:term : tactic => withMainContext do
  let hyp ← elabTerm h none
  let ty ← inferType hyp
  let some (_, lhs, _) := ty.eq? | throwError "not an equation"
  if lhs.getAppFn.constName? = some ``runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop then
    let theoremName := mkIdent `Itasca.Runtime.Compiler.compiler_locals_environment_frame
    evalTactic (← `(tactic| have effect := $theoremName $ops $law _ _ _ _ _ $h))
  else
    throwError "not local declaration loop"

macro "environment_frame_close" : tactic => `(tactic|
  (first | rfl | (simp_all [FunctionEnvironment, snapshotCompiler, source_unit_eq])))
macro "environment_frame_step " h:ident " using " ops:term ", " law:term : tactic => `(tactic|
  first
  | solve | (sources_terminal $h; environment_frame_close)
  | (fail_if_no_progress dsimp only at $h:ident)
  | solve | (environment_frame_effect $h using $ops, $law; environment_frame_close)
  | solve | (sources_terminal $h; have output := (Prod.mk.inj (Result.ok.injEq.mp $h)).2; cases output; environment_frame_close)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | (sources_nonterminal $h
     obtain ⟨value, called, rest⟩ := bind_ok_inv _ _ _ $h
     clear $h
     rename' rest => $h
     first
     | (guard_hyp value : Prod _ _; rcases value with ⟨firstValue, secondValue⟩)
     | skip
     try environment_frame_effect called using $ops, $law
     try clear called
     first
     | (guard_hyp firstValue : core.result.Result _ _; cases firstValue)
     | (guard_hyp value : core.result.Result _ _; cases value)
     | skip
     try simp only [uncurry_apply_pair] at $h:ident)
  | (fail_if_no_progress simp only [Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, bind_ok, bind_tc_ok] at $h:ident)
  | sources_split $h)

theorem compiler_add_local_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ty : Itasca.wasm_types.ValueType) (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.add_local ops before ty = .ok (status, after)) :
    FunctionEnvironment before after := by
  unfold runtime.compiler.FunctionCompiler.add_local at accepted
  repeat' environment_frame_step accepted using ops, law
theorem compiler_locals_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops)
    (before : runtime.compiler.FunctionCompiler A) (ctx : Itasca.code.Context) (index : Usize) (status : core.result.Result Unit Itasca.error.VisitError)
    (output : CompilerSnapshot A)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start_loop
      ops before ctx index status = .ok output) :
    FunctionEnvironment before (snapshotCompiler output) := by
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
        rfl
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
        exact (compiler_add_local_environment_frame ops law before middle site result patched).trans
          (ih _ smaller middle nextIndex result tail' rfl)
    · simp only [bind_ok, Result.ok.injEq] at accepted
      subst output
      rfl


theorem compiler_function_start_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    FunctionEnvironment before after := by
  unfold runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start at accepted
  repeat' environment_frame_step accepted using ops, law

end Itasca.Runtime.Compiler

end
