import Itasca.Runtime.Compiler.Local.Relations.Function.EnvironmentContracts
import Itasca.Runtime.Compiler.Local.Relations.Function.SignatureCapture
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Relations.Table.StatefulAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Callbacks.Table.CompilerAuxiliaryTables
import Itasca.Runtime.Compiler.Local.Relations.Local.LocalDeclarations
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Runtime.Compiler.Local.Relations.Layout.LayoutProofs
import Itasca.Support.Result
import Itasca.Runtime.Compiler.Local.Relations.Function.Function
import Itasca.Runtime.Compiler.Local.Relations.Emission.ScalarEmission

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
  exact runtime.compiler.CompileScheduler.capture_func_slots.total ops law scheduler env index ty lookup fits

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
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop1.total ops law scheduler env index status bound prefixMatches

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
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready_loop2.total ops law budget functions env index status bound initialized

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
  exact runtime.compiler.CompileScheduler.Insts.ItascaStreamStreamingVisitor.environment_ready.total ops law scheduler env emptyTypes emptySlots emptyFunctions

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
  obtain ⟨⟨status, after⟩, called, established⟩ := WP.spec_imp_exists
    (runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.total
      ops law compiler ctx typeIndex signature bodyBegin bodyEnd
      ⟨lookup, beginFits, endFits, emptyLocals, localLayout, emptyOperands, mapsFit, framesFit⟩)
  apply WP.exists_imp_spec ⟨(status, after), called, ?_⟩
  intro accepted
  obtain ⟨layout, _, _, _, _, _, _, _, code, frames, _⟩ := established accepted
  have frame := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.inv
    ops compiler after ctx typeIndex bodyBegin bodyEnd status called
  refine ⟨layout, code, frames, ?_⟩
  rw [frame]
  rfl

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
