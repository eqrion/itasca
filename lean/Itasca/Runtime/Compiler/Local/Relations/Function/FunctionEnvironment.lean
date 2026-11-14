import Itasca.Runtime.Compiler.Local.Relations.Function.SignatureCapture
import Itasca.Runtime.Compiler.Local.Callbacks.Function.FunctionStartContracts
import Itasca.Runtime.Compiler.Local.Initializer
import Itasca.Runtime.Compiler.Local.Callbacks.CallbackEquations
import Itasca.Runtime.Compiler.Local.Callbacks.Control.EnterIf
import Itasca.Runtime.Compiler.Local.Control.Segments.StructuredLabels
import Itasca.Support.Result
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
  exact runtime.compiler.CompileScheduler.capture_signature.total ops law scheduler env index ty lookup fits

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
  exact runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.total
    ops law compiler ctx typeIndex signature bodyBegin bodyEnd
    ⟨lookup, beginFits, endFits, emptyLocals, localLayout, emptyOperands, mapsFit, framesFit⟩

@[step] theorem compiler_new {A : Type} (ops : runtime.platform.Alloc A)
    (signatures : Slice runtime.compiler.Signature) (functionSlots : Slice U32)
    (budget : runtime.compiler.Budget A) (batchStart : Usize) :
    runtime.compiler.FunctionCompiler.new ops signatures functionSlots budget batchStart ⦃ out =>
      LocalLayout out ∧ out.function.locals.val = [] ∧ out.before.val = [] ∧
        out.function.controls.val = [] ∧ out.frames.val = [] ∧
        out.function.code.val = [] ∧ out.reachable = true ∧
        out.signatures = signatures ∧ out.func_param_slots = functionSlots ∧
        out.batch_start = batchStart ⦄ := by
  simp only [runtime.compiler.FunctionCompiler.new.eq, WP.spec_ok]
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
set_option maxRecDepth 4096

/-- Function entry and local declarations preserve the scheduler signature tables and batch origin. -/
def FunctionEnvironment {A : Type} (before after : runtime.compiler.FunctionCompiler A) : Prop :=
  (after.signatures, after.func_param_slots, after.batch_start) =
    (before.signatures, before.func_param_slots, before.batch_start)

theorem FunctionEnvironment.trans {A : Type} {before middle after : runtime.compiler.FunctionCompiler A}
    (first : FunctionEnvironment before middle) (second : FunctionEnvironment middle after) :
    FunctionEnvironment before after := Eq.trans second first




theorem compiler_function_start_environment_frame {A : Type} (ops : runtime.platform.Alloc A)
    (law : Platform.AllocCorrect ops) (before after : runtime.compiler.FunctionCompiler A)
    (ctx : Itasca.code.Context) (typeIndex : U32) (start finish : Usize)
    (status : core.result.Result Unit Itasca.error.VisitError)
    (accepted : runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start
      ops before ctx typeIndex start finish = .ok (status, after)) :
    FunctionEnvironment before after := by
  have frame := runtime.compiler.FunctionCompiler.Insts.ItascaCodeOpVisitor.on_function_start.inv
    ops before after ctx typeIndex start finish status accepted
  unfold FunctionEnvironment
  rw [frame]

end Itasca.Runtime.Compiler

end
