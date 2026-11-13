import Itasca.Runtime.Compiler.Local.Relations.Table.SignatureTable
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.TypeTranslation
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission
import Itasca.Support.EnvTranslation

/-!
Sections, each formerly its own module: Environment, FunctionStartRaw, CoreFunction, CoreFunctionContext.
-/

/-! ## Environment -/

section

/-!
Compiler environment preparation, including function-slot capture and the function-vector loop. The final environment-ready sequence is used by complete module assembly.
-/

/-! ## Function Slots -/

section

/-! Exact scheduler capture of argument word counts across the full source function index space. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem capture_function_slots {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (ty : Itasca.wasm_types.FuncType)
    (lookup : env.func_types.val[index.val]? = some ty)
    (fits : scheduler.func_param_slots.val.length < Usize.max) :
    runtime.compiler.CompileScheduler.capture_func_slots ops scheduler env index ⦃ out =>
      out.1 = .Ok () → ∃ word budget,
        out.2 = { scheduler with func_param_slots := out.2.func_param_slots, budget } ∧
        out.2.func_param_slots.val = scheduler.func_param_slots.val ++ [word] ∧
        word.val = signatureSlots ty.params.val ⦄ := by
  unfold runtime.compiler.CompileScheduler.capture_func_slots
  simp only [Itasca.metadata.Env.impl.func_types, bind_ok]
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  have inBounds : index.val < env.func_types.deref.length := by simpa [alloc.vec.Vec.deref] using bound
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
    step with budget_push ops law scheduler.budget scheduler.func_param_slots paramWords fits
      as ⟨status, budget, words, pushed⟩
    rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
    · simp only [runtime.compiler.visitor_result, bind_ok, WP.spec_ok]
      intro accepted
      refine ⟨paramWords, scheduler.budget, rfl, appended, ?_⟩
      simpa [alloc.vec.Vec.deref] using hparams
    · simp [runtime.compiler.visitor_result]

/-- Captured function parameter widths use the source function index space,
which includes imports, and preserve every previously captured type signature. -/
@[step] theorem capture_function_slots_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_types.val.length)
    (prefixMatches : status = .Ok () → scheduler.func_param_slots.val.map (fun word => word.val) =
      (env.func_types.val.take index.val).map (fun ty => signatureSlots ty.params.val)) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
      ops scheduler env index status ⦃ out =>
      out.2.2.2.2.2.2.2 = .Ok () →
        out.1 = scheduler.signatures ∧ out.2.1.val.map (fun word => word.val) =
          env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        out.2.2.2.1 = scheduler.functions ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1
  apply loop.spec_decr_nat (fun p => env.func_types.val.length - p.2.1.val)
    (fun p => p.2.1.val ≤ env.func_types.val.length ∧
      (p.2.2 = .Ok () → p.1.signatures = scheduler.signatures ∧
        p.1.func_param_slots.val.map (fun word => word.val) =
          (env.func_types.val.take p.2.1.val).map (fun ty => signatureSlots ty.params.val) ∧
        p.1.functions = scheduler.functions))
  · rintro ⟨current, i, result⟩ ⟨hi, certified⟩
    dsimp only at hi certified
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.body
    simp only [Itasca.metadata.Env.impl.func_types, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        obtain ⟨signaturesEq, currentMatches, sameFunctions⟩ := certified rfl
        have length := congrArg List.length currentMatches
        have capacity := env.func_types.property
        have fits : current.func_param_slots.val.length < Usize.max := by
          simp only [List.length_map, List.length_take, Nat.min_eq_left hi] at length
          omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with capture_function_slots ops law current env i env.func_types.val[i.val]
          (List.getElem?_eq_getElem hb) fits as ⟨answer, changed, effect⟩
        step as ⟨next, hnext⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro accepted
        obtain ⟨word, budget, changedEq, appended, exactWidth⟩ := effect accepted
        refine ⟨?_, ?_, ?_⟩
        · rw [changedEq]
          exact signaturesEq
        · rw [hnext, ← List.take_concat_get' env.func_types.val i.val hb, appended]
          simp only [List.map_append, List.map_singleton, currentMatches, exactWidth]
        · rw [changedEq]
          exact sameFunctions
    · rename_i finished
      have same : i.val = env.func_types.val.length := by simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using certified accepted
  · exact ⟨bound, fun accepted => ⟨rfl, prefixMatches accepted, rfl⟩⟩
end Itasca.Runtime.Compiler

end

/-! ## Prepare Functions -/

section

/-! Allocation-aware preparation of the defined-function result vector. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem prepare_functions_loop {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (budget : runtime.compiler.Budget A)
    (functions : alloc.vec.Vec (Option runtime.bytecode.CompiledFunction))
    (env : Itasca.metadata.Env) (index : Usize) (status : core.result.Result Unit Itasca.error.Error)
    (bound : index.val ≤ env.func_type_indices.val.length)
    (initialized : status = .Ok () → functions.val = List.replicate index.val none) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
      ops functions budget env index status ⦃ out =>
      out.2.2 = .Ok () → out.1.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2
  apply loop.spec_decr_nat (fun p => env.func_type_indices.val.length - p.2.2.1.val)
    (fun p => p.2.2.1.val ≤ env.func_type_indices.val.length ∧
      (p.2.2.2 = .Ok () → p.1.val = List.replicate p.2.2.1.val none))
  · rintro ⟨functions, budget, i, result⟩ ⟨hi, filled⟩
    dsimp only at hi filled
    unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.body
    simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
    split
    · rename_i more
      have hb : i.val < env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at more; scalar_tac
      cases result with
      | Err error => simp [core.result.Result.is_ok]
      | Ok unit =>
        cases unit
        have initialized := filled rfl
        have capacity := env.func_type_indices.property
        have fits : functions.val.length < Usize.max := by simp [initialized]; omega
        simp only [core.result.Result.is_ok, bind_ok, ite_true]
        step with budget_push ops law budget functions none fits as ⟨status, nextBudget, nextFunctions, pushed⟩
        rcases pushed with ⟨rfl, rfl, appended⟩ | ⟨rfl, rfl, rejected⟩
        · simp only [runtime.compiler.visitor_result, bind_ok]
          step as ⟨next, hnext⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro _
          rw [appended, initialized, hnext, List.replicate_add]
          simp
        · simp only [runtime.compiler.visitor_result, bind_ok]
          step as ⟨next, hnext⟩
          exact ⟨by scalar_tac, by simp, by scalar_tac⟩
    · rename_i finished
      have same : i.val = env.func_type_indices.val.length := by
        simp [alloc.vec.Vec.deref, Slice.len] at finished; scalar_tac
      simp only [WP.spec_ok]
      intro accepted
      simpa [same] using filled accepted
  · exact ⟨bound, initialized⟩
end Itasca.Runtime.Compiler

end

/-! ## Environment -/

section

/-! The actual scheduler environment callback constructs source type/signature
metadata and initializes every defined-function result slot. -/
namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

@[step] theorem compiler_environment_ready_sequence {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (scheduler : runtime.compiler.CompileScheduler A)
    (env : Itasca.metadata.Env) (emptyTypes : scheduler.signatures.val = [])
    (emptySlots : scheduler.func_param_slots.val = []) (emptyFunctions : scheduler.functions.val = []) :
    runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready ops scheduler env ⦃ out =>
      ∀ config, out.1 = .Ok config →
        SignatureSequence out.2.signatures.val env.types.val ∧
        out.2.func_param_slots.val.map (fun word => word.val) = env.func_types.val.map (fun ty => signatureSlots ty.params.val) ∧
        out.2.functions.val = List.replicate env.func_type_indices.val.length none ⦄ := by
  unfold runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready
  simp only [Itasca.metadata.Env.impl.func_type_indices, bind_ok]
  split
  · simp [runtime.compiler.Budget.reject]
  · simp only [Itasca.metadata.Env.impl.types, bind_ok]
    split
    · simp [runtime.compiler.Budget.reject]
    · step with capture_signatures_loop_frame ops law scheduler env 0#usize (.Ok ())
        (by simp) (by intro _; simp [emptyTypes, SignatureSequence])
        as ⟨signatures, words, completed, functions, tail, codeStart, budget, status, effect⟩
      cases status with
      | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok unit =>
        cases unit
        obtain ⟨sequence, slotsSame, functionsSame⟩ := effect rfl
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
        step with capture_function_slots_loop ops law
          ⟨signatures, words, completed, functions, tail, codeStart, budget⟩ env 0#usize (.Ok ())
          (by simp) (by intro _; simp [slotsSame, emptySlots])
          as ⟨signatures1, words1, completed1, functions1, tail1, codeStart1, budget1, status1, effect1⟩
        cases status1 with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
        | Ok unit =>
          cases unit
          obtain ⟨sameSignatures, slotsExact, functionsSame1⟩ := effect1 rfl
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, uncurry_apply_pair]
          step with prepare_functions_loop ops law budget1 functions1 env 0#usize (.Ok ())
            (by simp) (by intro _; simp [functionsSame1, functionsSame, emptyFunctions])
            as ⟨functions2, budget2, status2, effect2⟩
          cases status2 with
          | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
          | Ok unit =>
            cases unit
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
            intro config accepted
            refine ⟨?_, slotsExact, effect2 rfl⟩
            simpa only [sameSignatures] using sequence

end Itasca.Runtime.Compiler

end

end

/-! ## FunctionStartRaw -/

section

/-!
The successful function-start callback establishes the zero-operand layout, source coordinates, and the root control frame used by all later callbacks.

Main declarations: `compiler_function_start_raw`. A direct consumer is `Compiler.Local.Checking.OpenInstructionCompiler`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas Aeneas.Std

/-- The successful function-start callback establishes the zero-operand layout,
source coordinates, and the root control frame used by all later callbacks. -/
@[step] theorem compiler_function_start_raw {A : Type} (ops : runtime.platform.Alloc A)
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
        out.2.function.code = compiler.function.code ∧
        out.2.frames.val = compiler.frames.val ++
          [⟨0#usize, .Body, out.2.function.local_slots, 0#u32, signature.result_slots,
            0#u32, none, true, false, alloc.vec.Vec.new Usize⟩] ∧
        CompilerTables.ofFunction out.2.function = CompilerTables.ofFunction compiler.function ⦄ := by
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
          refine ⟨⟨layout.slots, layout.offsets, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
          · have : updated.before = compiler.before := by rw [frame]
            simp [this, emptyOperands, stackOffsets]
          · simp only [compilerLocals, slots, Nat.add_zero]
            exact layout.slots
          · intro _; exact Nat.le_refl _
          · rw [frame]
          · simpa [sameFrames] using frameAppend
          · rw [frame]
            rfl
        · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      · simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end Itasca.Runtime.Compiler

end

/-! ## CoreFunction -/

section

/-!
The source function context is fixed by the independently decoded module metadata and the function's parameter, local and result declarations.

Main declarations: `sourceFunctionContext`. A direct consumer is `Compiler.Local.Relations.Function.CoreFunctionContext`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- The source function context is fixed by the independently decoded module
metadata and the function's parameter, local and result declarations. -/
def sourceFunctionContext (env : Itasca.metadata.Env) (locals results : List valtype) : context :=
  { TYPES := env.types.val.map Itasca.EnvTranslation.funcType
    FUNCS := env.func_types.val.map Itasca.EnvTranslation.funcType
    GLOBALS := env.global_types.val.map Itasca.Translate.globalType
    TABLES := env.table_types.val.map Itasca.EnvTranslation.tableType
    MEMS := env.mem_types.val.map Itasca.EnvTranslation.memType
    ELEMS := Itasca.EnvTranslation.elementTypes env
    DATAS := Itasca.EnvTranslation.dataTypes env
    LOCALS := locals
    LABELS := []
    RETURN := some (.mk_list results) }

theorem source_function_context_reader (env : Itasca.metadata.Env) (ctx : Itasca.code.Context) :
    sourceFunctionContext env (ctx.locals.val.map Itasca.Translate.valueType)
      (ctx.results.val.map Itasca.Translate.valueType) = Itasca.EnvTranslation.context env ctx := rfl

end Itasca.Runtime.Compiler

end

/-! ## CoreFunctionContext -/

section

/-!
At module publication the complete data namespace comes from the parsed tail. Code validation may have run before that tail, without a data-count section; the supported scalar emission has no data-segment instruction.

Main declarations: `moduleFunctionContext`. A direct consumer is `Integration.Instantiation.InstantiateExecutableEventfulOrigin`.
-/

namespace Itasca.Runtime.Compiler
open Aeneas.Std

/-- Emission depends exactly on the local/global/memory namespaces used by
this instruction grammar. Other source namespaces may be completed by parsing
the module tail without changing any emitted instruction. -/
theorem ScalarEmission.context {C D before instruction emitted after}
    (locals : D.LOCALS = C.LOCALS) (globals : D.GLOBALS = C.GLOBALS)
    (memories : D.MEMS = C.MEMS)
    (emission : ScalarEmission C before instruction emitted after) :
    ScalarEmission D before instruction emitted after := by
  cases emission with
  | linear h => exact .linear (by simpa only [locals] using h)
  | float32 stack dst bits slot => exact .float32 _ dst bits (by simpa only [locals] using slot)
  | float64 stack dst bits slot => exact .float64 _ dst bits (by simpa only [locals] using slot)
  | select stack ty left right condition leftSlot rightSlot conditionSlot =>
    exact .select _ ty left right condition (by simpa only [locals] using leftSlot) rightSlot conditionSlot
  | globalGet stack mutability ty index dst found slot =>
    exact .globalGet _ mutability ty index dst (by simpa only [globals] using found) (by simpa only [locals] using slot)
  | globalSet stack ty index src found slot =>
    exact .globalSet _ ty index src (by simpa only [globals] using found) (by simpa only [locals] using slot)
  | load stack op arg address offset memory found source slot =>
    exact .load _ op arg address offset memory (by simpa only [memories] using found) source (by simpa only [locals] using slot)
  | store stack op arg address value offset memory found source addressSlot valueSlot =>
    exact .store _ op arg address value offset memory (by simpa only [memories] using found) source
      (by simpa only [locals] using addressSlot) valueSlot
  | float stack op left right leftSlot rightSlot =>
    exact .float stack op left right (by simpa only [locals] using leftSlot) rightSlot

/-- At module publication the complete data namespace comes from the parsed
tail. Code validation may have run before that tail, without a data-count
section; the supported scalar emission has no data-segment instruction. -/
def moduleFunctionContext (module : runtime.compiler.ExecutableModule)
    (locals results : List valtype) : context :=
  {sourceFunctionContext module.module.env locals results with
    DATAS := List.replicate module.module.tail.data.length datatype.OK}

end Itasca.Runtime.Compiler

end
